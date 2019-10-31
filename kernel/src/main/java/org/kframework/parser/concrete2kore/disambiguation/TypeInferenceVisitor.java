// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.builtin.Sorts;
import org.kframework.definition.Production;
import org.kframework.definition.NonTerminal;
import org.kframework.kore.Sort;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.VariableTypeClashException;

import org.pcollections.ConsPStack;

import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.Collections;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

public class TypeInferenceVisitor extends SetsTransformerWithErrors<ParseFailedException> {
  private final TypeInferencer inferencer;
  private final boolean inferSortChecks;
  private final boolean inferCasts;
  private final boolean isAnywhere;
  private final Sort topSort;
  public TypeInferenceVisitor(TypeInferencer inferencer, Sort topSort, boolean inferSortChecks, boolean inferCasts, boolean isAnywhere) {
    this.inferencer = inferencer;
    this.topSort = topSort;
    this.inferSortChecks = inferSortChecks;
    this.inferCasts = inferCasts;
    this.isAnywhere = isAnywhere;
  }

  @Override
  public Either<Set<ParseFailedException>, Term> apply(Term t) {
    Term loc = t;
    if (loc instanceof Ambiguity) {
      loc = ((Ambiguity)loc).items().iterator().next();
    }
    inferencer.push(t, topSort, isAnywhere);
    Either<Set<ParseFailedException>, Term> typed;
    try {
      if (inferencer.hasNoVariables()) {
        return Right.apply(t);
      }
      switch(inferencer.status()) {
      case SATISFIABLE:
        break;
      case UNKNOWN:
        throw KEMException.internalError("Could not solve sort constraints.", t);
      case UNSATISFIABLE:
        Set<ParseFailedException> kex = inferencer.error();
        return Left.apply(kex);
      }
      inferencer.computeModel();
      typed = new TypeCheckVisitor(topSort).apply(t);
      if (typed.isLeft()) {
        return typed;
      }
      inferencer.pushNotModel(typed.right().get());
      TypeInferencer.Status status = inferencer.status();
      switch(status) {
      case SATISFIABLE:
        Set<ParseFailedException> kex = inferencer.error();
        return Left.apply(kex);
      case UNKNOWN:
        throw KEMException.internalError("Could not solve sort constraints.", t);
      case UNSATISFIABLE:
        return typed;
      }
      throw new AssertionError();
    } finally {
      inferencer.pop();
    }
  }

  public class TypeCheckVisitor extends SetsTransformerWithErrors<ParseFailedException> {

    private Sort expectedSort;
    private boolean hasCastAlready = false, hasCheckAlready = false;
    public TypeCheckVisitor(Sort topSort) {
      this.expectedSort = topSort;
    }

    private Either<Set<ParseFailedException>, Term> typeError(ProductionReference pr, Sort expectedSort, Sort actualSort) {
      String msg;
      if (pr instanceof Constant) {
        msg = "Unexpected sort " + actualSort + " for term " + ((Constant)pr).value() + ". Expected " + expectedSort + ".";
      } else {
        msg = "Unexpected sort " + actualSort + " for term parsed as production " + pr.production() + ". Expected " + expectedSort + ".";
      }
      KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, pr.source().orElse(null), pr.location().orElse(null));
      return Left.apply(Collections.singleton(new VariableTypeClashException(kex)));
    }

    @Override
    public Either<Set<ParseFailedException>, Term> apply(Term term) {
      if (term instanceof Ambiguity) {
        Ambiguity amb = (Ambiguity)term;
        return super.apply(amb);
      }
      ProductionReference pr = (ProductionReference)term;
      if (pr instanceof Constant && pr.production().sort().equals(Sorts.KVariable())) {
        Sort inferred = inferencer.getArgs(pr).apply(0);
        if (!inferencer.module().subsorts().lessThanEq(inferred, expectedSort) && !expectedSort.equals(Sorts.KVariable())) {
          return typeError(pr, expectedSort, inferred);
        }
        return wrapTermWithCast((Constant)pr, inferred);
      }
      Production substituted = pr.production().substitute(inferencer.getArgs(pr));
      Sort actualSort = substituted.sort();
      if (!inferencer.module().subsorts().lessThanEq(actualSort, expectedSort)) {
        return typeError(pr, expectedSort, actualSort);
      }
      if (pr instanceof TermCons) {
        TermCons tc = (TermCons)pr;
        for (int i = 0, j = 0; i < substituted.items().size(); i++) {
          if (substituted.items().apply(i) instanceof NonTerminal) {
            boolean wasCast = hasCastAlready;
            boolean wasCheck = hasCheckAlready;
            if (substituted.klabel().isDefined() && substituted.klabel().get().name().startsWith("#SemanticCastTo")) {
              hasCheckAlready = true;
              hasCastAlready = true;
            } else if (substituted.klabel().isDefined() &&
                    (substituted.klabel().get().name().equals("#SyntacticCast") ||
                            substituted.klabel().get().name().equals("#InnerCast"))) {
              hasCastAlready = true;
              hasCheckAlready = false;
            } else {
              hasCastAlready = false;
              hasCheckAlready = false;
            }
            Term t = tc.get(j);
            Sort oldExpected = expectedSort;
            expectedSort = ((NonTerminal) substituted.items().apply(i)).sort();
            Either<Set<ParseFailedException>, Term> rez = apply(t);
            expectedSort = oldExpected;
            hasCastAlready = wasCast;
            hasCheckAlready = wasCheck;
            if (rez.isLeft())
              return rez;
            tc = tc.with(j, rez.right().get());
            j++;
          }
        }
        return Right.apply(tc);
      }
      return Right.apply(pr);
    }

    private Either<Set<ParseFailedException>, Term> wrapTermWithCast(Constant c, Sort declared) {
      Production cast;
      if (inferSortChecks && !hasCheckAlready) {
          cast = inferencer.module().productionsFor().apply(KLabel("#SemanticCastTo" + declared.toString())).head();
      } else if (inferCasts && !hasCastAlready && inferencer.module().productionsFor().contains(KLabel("#SyntacticCast"))) {
          cast = stream(inferencer.module().productionsFor().apply(KLabel("#SyntacticCast"))).filter(p -> p.sort().equals(declared)).findAny().get();
      } else {
          cast = null;
      }
      if (cast == null) {
          return Right.apply(c);
      } else {
          return Right.apply(TermCons.apply(ConsPStack.singleton(c), cast, c.location(), c.source()));
      }
    }
  }
}

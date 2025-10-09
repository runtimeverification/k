// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.kframework.builtin.Sorts;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.kore.Sort;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

/**
 * Disambiguation transformer which performs type checking and variable type inference.
 *
 * <p>This class is responsible for most of the interaction at the K level, the overall driving of
 * the disambiguation algorithm, and the pruning of ill-typed branches from the parse forest. All of
 * the z3 code is managed by {@link TypeInferencer}.
 *
 * <p>At a high level, the algorithm does the following:
 *
 * <p>1. Define all the sorts in z3 and the subsort relationship between sorts. 2. Declare all the
 * variables and sort parameters in the term as z3 constants. 3. Assert that the sort parameters are
 * not sort KLabel. 4. While preserving sharing, assert the constraints that determine whether the
 * term is well-typed. 5. Add soft constraints indicating that we prefer larger solutions to smaller
 * solutions. These serve as a heuristic only and do not exhaustively describe maximality. Their
 * purpose is simply to cut the search space. 6. Check satisfiability. If the constraints cannot be
 * satisfied, replay the constraints one at a time to determine the constraint at which the solution
 * becomes unsatisfiable, and use the model of the last constraint to be satisfied to generate a
 * type error. Otherwise: 7. Assert that the variables are not less than or equal to the model of
 * the first solution, and check for another solution. Repeat this in a loop until the constraints
 * become unsatisfied. 8. Filter out all models which are strictly less than some other model we
 * have obtained. 9. For each remaining model, substitute the sorts of the variables into the term
 * and trim out the branches of the parse forest for which that solution is not well typed. 10.
 * Disjunct the substituted solutions together and return them.
 */
public class TypeInferenceVisitor extends SetsTransformerWithErrors<KEMException> {
  private final TypeInferencer inferencer;
  private final boolean isAnywhere;
  private final Sort topSort;

  /**
   * @param inferencer
   * @param topSort The expected sort of the top of the term.
   * @param isAnywhere true if the term is an anywhere rule
   */
  public TypeInferenceVisitor(TypeInferencer inferencer, Sort topSort, boolean isAnywhere) {
    this.inferencer = inferencer;
    this.topSort = topSort;
    this.isAnywhere = isAnywhere;
  }

  @Override
  public Either<Set<KEMException>, Term> apply(Term t) {
    // add constraints to inferencer
    inferencer.push(t, topSort, isAnywhere);
    try {
      if (inferencer.hasNoVariables()) {
        // skip the rest as there is nothing to infer
        return Right.apply(t);
      }
      switch (inferencer.status()) {
        case SATISFIABLE -> {
          // there is at least one solution, so compute it and pop the soft constraints
          inferencer.computeModel();
          inferencer.pop();
        }
        case UNKNOWN -> {
          // constraints could not be solved, so error
          inferencer.pop();
          throw KEMException.internalError("Could not solve sort constraints.", t);
        }
        case UNSATISFIABLE -> {
          // no solutions exist. This is a type error, so ask the inferencer for an error message
          // and return
          inferencer.pop();
          Set<KEMException> kex = inferencer.error();
          return Left.apply(kex);
        }
      }
      boolean hasAnotherSolution = true;
      Set<Map<String, Sort>> models = new HashSet<>();
      boolean once = true;
      do {
        // compute the last solution except the first time through the loop, when it was already
        // done
        if (!once) {
          inferencer.computeModel();
        }
        once = false;
        boolean isMaximal = false;
        do {
          inferencer.pushGreater();
          switch (inferencer.status()) {
            case SATISFIABLE -> {
              // is not maximal, keep going
              isMaximal = false;
              inferencer.computeModel();
              inferencer.pop();
            }
            case UNKNOWN ->
                // constraints coiuld not be solved, so error
                throw KEMException.internalError("Could not solve sortconstraints.", t);
            case UNSATISFIABLE -> {
              isMaximal = true;
              inferencer.pop();
            }
          }
        } while (!isMaximal);
        models.add(inferencer.getModel());
        // assert that we don't want any solutions less than this one
        inferencer.pushNotModel();
        hasAnotherSolution =
            switch (inferencer.status()) {
              case SATISFIABLE ->
                  // found another solution, keep going
                  true;
              case UNKNOWN ->
                  // constraints could not be solved, so error
                  throw KEMException.internalError("Could not solve sort constraints.", t);
              case UNSATISFIABLE ->
                  // no more solutions, terminate loop
                  false;
            };
      } while (hasAnotherSolution);
      // remove all models that are not maximal
      Set<Term> candidates = new HashSet<>();
      Set<KEMException> exceptions = new HashSet<>();
      for (Map<String, Sort> model : models) {
        // for each model, apply it to the term
        inferencer.selectModel(model);
        Either<Set<KEMException>, Term> result = new TypeCheckVisitor(topSort).apply(t);
        if (result.isLeft()) {
          exceptions.addAll(result.left().get());
        } else {
          candidates.add(result.right().get());
        }
      }
      // return disjunction of solutions if there is multiple, otherwise return the only solution.
      if (candidates.isEmpty()) {
        return Left.apply(exceptions);
      } else if (candidates.size() == 1) {
        return Right.apply(candidates.iterator().next());
      } else {
        return Right.apply(Ambiguity.apply(candidates));
      }
    } finally {
      inferencer.pop();
    }
  }

  /**
   * A transformer which takes a particular type inference solution and applies it to a given term.
   *
   * <p>Essentially, for each term in the parse forest, we compute the actual sort of the term from
   * the model, and compare it to the expected sort. If it is not well typed, we remove that branch
   * of the parse forest entirely. We also, depending on the flags passed to the parent class, might
   * add casts to the term around variables.
   */
  public class TypeCheckVisitor extends SetsTransformerWithErrors<KEMException> {

    private Sort expectedSort;

    private enum CastContext {
      NONE,
      SEMANTIC,
      STRICT
    };

    private CastContext castContext = CastContext.NONE;

    public TypeCheckVisitor(Sort topSort) {
      this.expectedSort = topSort;
    }

    private Either<Set<KEMException>, Term> typeError(
        ProductionReference pr, Sort expectedSort, Sort actualSort) {
      String msg;
      if (pr instanceof Constant) {
        msg =
            "Unexpected sort "
                + actualSort
                + " for term "
                + ((Constant) pr).value()
                + ". Expected "
                + expectedSort
                + ".";
      } else {
        msg =
            "Unexpected sort "
                + actualSort
                + " for term parsed as production "
                + pr.production()
                + ". Expected "
                + expectedSort
                + ".";
      }
      return Left.apply(Collections.singleton(KEMException.innerParserError(msg, pr)));
    }

    @Override
    public Either<Set<KEMException>, Term> apply(Term term) {
      if (term instanceof Ambiguity amb) {
        return super.apply(amb);
      }
      ProductionReference pr = (ProductionReference) term;
      if (pr instanceof Constant
          && (pr.production().sort().equals(Sorts.KVariable())
              || pr.production().sort().equals(Sorts.KConfigVar()))) {
        // this is a variable, so check that its inferred sort is less than or equal to the expected
        // sort
        Sort inferred = inferencer.getArgs(pr).apply(0);
        if (!inferencer.module().subsorts().lessThanEq(inferred, expectedSort)
            && !expectedSort.equals(Sorts.KVariable())) {
          // this variable is not well typed at this location, so prune this branch
          return typeError(pr, expectedSort, inferred);
        }
        // well typed, so add a cast and return
        return wrapTermWithCast(pr, inferred);
      }
      // compute the instantiated production with its sort parameters
      Production substituted = pr.production().substitute(inferencer.getArgs(pr));
      Sort actualSort = substituted.sort();
      boolean isExactSort = castContext == CastContext.STRICT;
      // check type: inner casts and syntactic casts indicate type equality, everything else is <=
      if ((isExactSort && !actualSort.equals(expectedSort))
          || (!isExactSort
              && !inferencer.module().subsorts().lessThanEq(actualSort, expectedSort))) {
        // not well typed, so prune this branch
        return typeError(pr, expectedSort, actualSort);
      }
      // check types of children
      if (pr instanceof TermCons tc) {
        for (int i = 0, j = 0; i < substituted.items().size(); i++) {
          if (substituted.items().apply(i) instanceof NonTerminal) {
            // save prior value of variables
            CastContext oldContext = castContext;
            // compute whether this is a cast already
            if (substituted.klabel().isDefined()
                && substituted.klabel().get().name().startsWith("#SemanticCastTo")) {
              castContext = CastContext.SEMANTIC;
            } else if (substituted.klabel().isDefined()
                && (substituted.klabel().get().name().equals("#SyntacticCast")
                    || substituted.klabel().get().name().equals("#SyntacticCastBraced"))) {
              castContext = CastContext.STRICT;
            } else {
              castContext = CastContext.NONE;
            }
            Term t = tc.get(j);
            Sort oldExpected = expectedSort;
            // compute expected sort of child
            expectedSort = ((NonTerminal) substituted.items().apply(i)).sort();
            // recurse
            Either<Set<KEMException>, Term> rez = apply(t);
            // restore values
            expectedSort = oldExpected;
            castContext = oldContext;
            if (rez.isLeft()) return rez;
            // apply result of visiting child to the term.
            tc = tc.with(j, rez.right().get());
            j++;
          }
        }
        if (pr.production().params().nonEmpty() && hasParametricSort(pr.production())) {
          return wrapTermWithCast(tc, substituted.sort());
        }
        return Right.apply(tc);
      }
      return Right.apply(pr);
    }

    private boolean hasParametricSort(Production prod) {
      if (prod.sort().head().params() != 0) {
        return true;
      }
      if (stream(prod.nonterminals()).anyMatch(nt -> nt.sort().head().params() != 0)) {
        return true;
      }
      return false;
    }

    private Either<Set<KEMException>, Term> wrapTermWithCast(
        ProductionReference pr, Sort declared) {
      if (castContext != CastContext.SEMANTIC) {
        // There isn't an existing :Sort, so add one
        Production cast =
            inferencer
                .module()
                .productionsFor()
                .apply(KLabel("#SemanticCastTo" + declared.toString()))
                .head();
        return Right.apply(
            TermCons.apply(ConsPStack.singleton(pr), cast, pr.location(), pr.source()));
      }
      return Right.apply(pr);
    }
  }
}

// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

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

import org.pcollections.ConsPStack;

import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * Disambiguation transformer which performs type checking and variable type inference.
 *
 * This class is responsible for most of the interaction at the K level, the overall driving of the disambiguation
 * algorithm, and the pruning of ill-typed branches from the parse forest. All of the z3 code is managed by
 * {@link TypeInferencer}.
 *
 * At a high level, the algorithm does the following:
 *
 * 1.  Define all the sorts in z3 and the subsort relationship between sorts.
 * 2.  Declare all the variables and sort parameters in the term as z3 constants.
 * 3.  Assert that the sort parameters are not sort KLabel.
 * 4.  While preserving sharing, assert the constraints that determine whether the term is well-typed.
 * 5.  Add soft constraints indicating that we prefer larger solutions to smaller solutions. These serve as a heuristic
 *     only and do not exhaustively describe maximality. Their purpose is simply to cut the search space.
 * 6.  Check satisfiability. If the constraints cannot be satisfied, replay the constraints one at a time to determine
 *     the constraint at which the solution becomes unsatisfiable, and use the model of the last constraint to be
 *     satisfied to generate a type error. Otherwise:
 * 7.  Assert that the variables are not less than or equal to the model of the first solution, and check for another
 *     solution. Repeat this in a loop until the constraints become unsatisfied.
 * 8.  Filter out all models which are strictly less than some other model we have obtained.
 * 9.  For each remaining model, substitute the sorts of the variables into the term and trim out the branches of the
 *     parse forest for which that solution is not well typed.
 * 10. Disjunct the substituted solutions together and return them.
 *
 */
public class TypeInferenceVisitor extends SetsTransformerWithErrors<KEMException> {
  private final TypeInferencer inferencer;
  private final boolean inferSortChecks;
  private final boolean inferCasts;
  private final boolean isAnywhere;
  private final Sort topSort;

  /**
   *
   * @param inferencer
   * @param topSort  The expected sort of the top of the term.
   * @param inferSortChecks true if we should add :Sort to variables
   * @param inferCasts true if we should add ::Sort to variables
   * @param isAnywhere true if the term is an anywhere rule
   */
  public TypeInferenceVisitor(TypeInferencer inferencer, Sort topSort, boolean inferSortChecks, boolean inferCasts, boolean isAnywhere) {
    this.inferencer = inferencer;
    this.topSort = topSort;
    this.inferSortChecks = inferSortChecks;
    this.inferCasts = inferCasts;
    this.isAnywhere = isAnywhere;
  }

  @Override
  public Either<Set<KEMException>, Term> apply(Term t) {
    Term loc = t;
    if (loc instanceof Ambiguity) {
      loc = ((Ambiguity)loc).items().iterator().next();
    }
    // add constraints to inferencer
    inferencer.push(t, topSort, isAnywhere);
    Either<Set<KEMException>, Term> typed;
    try {
      if (inferencer.hasNoVariables()) {
        // skip the rest as there is nothing to infer
        return Right.apply(t);
      }
      switch(inferencer.status()) {
      case SATISFIABLE:
        // there is at least one maximal solution, so compute it
        inferencer.computeModel();
        break;
      case UNKNOWN:
        // constraints could not be solved, so error
        throw KEMException.internalError("Could not solve sort constraints.", t);
      case UNSATISFIABLE:
        // no solutions exist. This is a type error, so ask the inferencer for an error message and return
        Set<KEMException> kex = inferencer.error();
        return Left.apply(kex);
      }
      boolean hasAnotherSolution = true;
      Set<Map<String, Sort>> models = new HashSet<>();
      boolean once = true;
      do {
        // compute the last solution except the first time through the loop, when it was already done
        if (!once) {
          inferencer.computeModel();
        }
        once = false;
        models.add(inferencer.getModel());
        // assert that we don't want any solutions less than this one
        inferencer.pushNotModel();
        switch(inferencer.status()) {
        case SATISFIABLE:
          // found another solution, keep going
          hasAnotherSolution = true;
          break;
        case UNKNOWN:
          // constraints could not be solved, so error
          throw KEMException.internalError("Could not solve sort constraints.", t);
        case UNSATISFIABLE:
          // no more solutions, terminate loop
          hasAnotherSolution = false;
          break;
        }
      } while (hasAnotherSolution);
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
   * Check whether one model is less than or equal to another
   * @param model1
   * @param model2
   * @return
   */
  public boolean lessThanEq(Map<String, Sort> model1, Map<String, Sort> model2) {
    for (Map.Entry<String, Sort> model1Entry : model1.entrySet()) {
      if (model1Entry.getKey().startsWith("Var")) {
        Sort model1Sort = model1Entry.getValue();
        Sort model2Sort = model2.get(model1Entry.getKey());
        if (!inferencer.module().syntacticSubsorts().lessThanEq(model1Sort, model2Sort)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Compute the list of maximal models from a set of models
   * @param models All the models
   * @return The models in the input which are not strictly less than some other model.
   */
  public List<Map<String, Sort>> removeNonMaximal(Set<Map<String, Sort>> models) {
    List<Map<String, Sort>> maximals = new ArrayList<>();
    outer:
    for (Map<String, Sort> candidate : models) {
      for (Iterator<Map<String, Sort>> it = maximals.iterator(); it.hasNext();) {
        Map<String, Sort> maximal = it.next();
        if (lessThanEq(candidate, maximal)) {
          continue outer;
        } else if (lessThanEq(maximal, candidate)) {
          it.remove();
        }
      }
      maximals.add(new HashMap<>(candidate));
    }
    return maximals;
  }

  /**
   * A transformer which takes a particular type inference solution and applies it to a given term.
   *
   * Essentially, for each term in the parse forest, we compute the actual sort of the term from the model, and compare
   * it to the expected sort. If it is not well typed, we remove that branch of the parse forest entirely. We also,
   * depending on the flags passed to the parent class, might add casts to the term around variables.
   */
  public class TypeCheckVisitor extends SetsTransformerWithErrors<KEMException> {

    private Sort expectedSort;
    private boolean hasCastAlready = false, hasCheckAlready = false;
    public TypeCheckVisitor(Sort topSort) {
      this.expectedSort = topSort;
    }

    private Either<Set<KEMException>, Term> typeError(ProductionReference pr, Sort expectedSort, Sort actualSort) {
      String msg;
      if (pr instanceof Constant) {
        msg = "Unexpected sort " + actualSort + " for term " + ((Constant)pr).value() + ". Expected " + expectedSort + ".";
      } else {
        msg = "Unexpected sort " + actualSort + " for term parsed as production " + pr.production() + ". Expected " + expectedSort + ".";
      }
      return Left.apply(Collections.singleton(KEMException.innerParserError(msg, pr)));
    }

    @Override
    public Either<Set<KEMException>, Term> apply(Term term) {
      if (term instanceof Ambiguity) {
        Ambiguity amb = (Ambiguity)term;
        return super.apply(amb);
      }
      ProductionReference pr = (ProductionReference)term;
      if (pr instanceof Constant && (pr.production().sort().equals(Sorts.KVariable()) || pr.production().sort().equals(Sorts.KConfigVar()))) {
        // this is a variable, so check that its inferred sort is less than or equal to the expected sort
        Sort inferred = inferencer.getArgs(pr).apply(0);
        if (!inferencer.module().subsorts().lessThanEq(inferred, expectedSort) && !expectedSort.equals(Sorts.KVariable())) {
          // this variable is not well typed at this location, so prune this branch
          return typeError(pr, expectedSort, inferred);
        }
        // well typed, so add a cast and return
        return wrapTermWithCast((Constant)pr, inferred);
      }
      // compute the instantiated production with its sort parameters
      Production substituted = pr.production().substitute(inferencer.getArgs(pr));
      Sort actualSort = substituted.sort();
      boolean isExactSort = hasCastAlready && !hasCheckAlready;
      // check type: inner casts and syntactic casts indicate type equality, everything else is <=
      if ((isExactSort && !actualSort.equals(expectedSort)) || (!isExactSort && !inferencer.module().subsorts().lessThanEq(actualSort, expectedSort))) {
        // not well typed, so prune this branch
        return typeError(pr, expectedSort, actualSort);
      }
      // check types of children
      if (pr instanceof TermCons) {
        TermCons tc = (TermCons)pr;
        for (int i = 0, j = 0; i < substituted.items().size(); i++) {
          if (substituted.items().apply(i) instanceof NonTerminal) {
            // save prior value of variables
            boolean wasCast = hasCastAlready;
            boolean wasCheck = hasCheckAlready;
            // compute whether this is a cast already
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
            // compute expected sort of child
            expectedSort = ((NonTerminal) substituted.items().apply(i)).sort();
            // recurse
            Either<Set<KEMException>, Term> rez = apply(t);
            // restore values
            expectedSort = oldExpected;
            hasCastAlready = wasCast;
            hasCheckAlready = wasCheck;
            if (rez.isLeft())
              return rez;
            // apply result of visiting child to the term.
            tc = tc.with(j, rez.right().get());
            j++;
          }
        }
        return Right.apply(tc);
      }
      return Right.apply(pr);
    }

    private Either<Set<KEMException>, Term> wrapTermWithCast(Constant c, Sort declared) {
      Production cast;
      if (inferSortChecks && !hasCheckAlready) {
        // strictly typing variables and one does not already exist, so add :Sort
        cast = inferencer.module().productionsFor().apply(KLabel("#SemanticCastTo" + declared.toString())).head();
      } else if (inferCasts && !hasCastAlready && inferencer.module().productionsFor().contains(KLabel("#SyntacticCast"))) {
        // casting variables and one doeds not already exist, so add ::Sort
        cast = stream(inferencer.module().productionsFor().apply(KLabel("#SyntacticCast"))).filter(p -> p.sort().equals(declared)).findAny().get();
      } else {
        // unparsing or cast already exists, so do nothing
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

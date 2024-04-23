// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

/**
 * Disambiguation transformer which performs type checking and infers the sorts of variables.
 *
 * <p>The overall design is heavily inspired by the algorithm described in "The Simple Essence of
 * Algebraic Subtyping: Principal Type Inference with Subtyping Made Easy" by Lionel Parreaux.
 *
 * <p>Each Term can be viewed as a SimpleSub-esque term with equivalent subtyping constraints:
 *
 * <ul>
 *   <li>Each Production is a function symbol whose input types are the sorts of its non-terminals
 *       and whose output type is the sort of the overall Production.
 *   <li>Each ProductionReference is an application of the corresponding Production function symbol
 *       to its arguments.
 *   <li>The Term as a whole is a function, treating each variable in the Term as a variable bound
 *       at the top level of the Term.
 * </ul>
 *
 * Inferring the SimpleSub-esque type is then equivalent to performing SortInference. That is, we
 * infer a type a1 -> ... aN -> b telling us that the variables x1, ..., xN have sorts a1, ..., aN
 * and the overall Term has sort b.
 *
 * <p>Explicitly, the algorithm proceeds as follows
 *
 * <ol>
 *   <li>Infer a BoundedSort for the input Term as well as all of its variables, recording each
 *       subtype constraint as lower and upper bounds on sort variables.
 *       <ul>
 *         <li>BoundedSort is directly analogous to SimpleType from SimpleSub, except that we only
 *             have primitive sorts (BoundedSort.Constructor) and variables (BoundedSort.Variable).
 *         <li>TermSort represents the "function type" of the overall Term
 *       </ul>
 *   <li>Constrain the inferred BoundedSort of the overall Term as a subsort of the expected
 *       topSort.
 *   <li>Compactify then simplify the TermSort to produce a CompactSort (analogous to producing the
 *       CompactType in SimpleSub).
 *   <li>Convert the inferred CompactSort into a normal K Sort
 *       <ul>
 *         <li>Monomorphize each sort variable, allowing it to take any value between its recorded
 *             bounds and possibly producing multiple valid monomorphizations.
 *         <li>For each type intersection/union, actually compute the corresponding meet/join on the
 *             subsort poset, erroring if no such meet/join exists.
 *       </ul>
 *   <li>Insert a SemanticCast around every variable in the Term to record the results.
 * </ol>
 */
public class SortInferencer {
  private final Module mod;

  public SortInferencer(Module mod) {
    this.mod = mod;
  }

  /**
   * Determine whether a Term is supported by the current SortInferencer algorithm. Supported terms
   * can contain neither ambiguities nor parametric sorts.
   */
  public static boolean isSupported(Term t) {
    return !hasAmbiguity(t) && !hasParametricSorts(t);
  }

  private static boolean hasAmbiguity(Term t) {
    if (t instanceof Ambiguity) {
      return true;
    }
    if (t instanceof Constant) {
      return false;
    }
    return ((TermCons) t).items().stream().anyMatch(SortInferencer::hasAmbiguity);
  }

  private static boolean hasParametricSorts(Term t) {
    if (t instanceof Ambiguity amb) {
      return amb.items().stream().anyMatch(SortInferencer::hasParametricSorts);
    }
    ProductionReference pr = (ProductionReference) t;
    if (stream(pr.production().items())
        .filter(pi -> pi instanceof NonTerminal)
        .map(pi -> ((NonTerminal) pi).sort())
        .anyMatch(s -> !s.params().isEmpty())) {
      return true;
    }
    if (!pr.production().sort().params().isEmpty()) {
      return true;
    }
    if (pr instanceof Constant) {
      return false;
    }
    return ((TermCons) t).items().stream().anyMatch(SortInferencer::hasParametricSorts);
  }

  /**
   * Determine if a term is a rule which can be applied anywhere in a configuration, and thus does
   * not permit the RHS sort to be wider than the LHS. Such a rule is either explicitly marked with
   * an attribute, or is a function or macro rule.
   *
   * @param isAnywhere - Whether the Term was explicitly marked with an attribute such as anywhere,
   *     simplification, macro, etc. indicating that it is a rule which applies anywhere
   */
  private static boolean isAnywhereRule(Term t, boolean isAnywhere) {
    if (t instanceof Ambiguity) {
      throw new AssertionError("Ambiguities are not yet supported!");
    }
    t = stripBrackets(t);
    if (t instanceof Constant) {
      return false;
    }
    TermCons tc = (TermCons) t;
    // For every #RuleContent production, the first non-terminal holds a #RuleBody
    if (tc.production().sort().equals(Sorts.RuleContent())) {
      assert tc.production().nonterminals().size() >= 1
          && tc.production().nonterminal(0).sort().equals(Sorts.RuleBody());
      return isAnywhereRule(tc.get(0), isAnywhere);
    }
    // For every #RuleBody production, the first non-terminal holds the actual K term
    if (tc.production().sort().equals(Sorts.RuleBody())) {
      assert tc.production().nonterminals().size() >= 1
          && tc.production().nonterminal(0).sort().equals(Sorts.K());
      return isAnywhereRule(tc.get(0), isAnywhere);
    }
    // This is the first actual K term we encounter after stripping away rule syntax,
    // and should be a rewrite if this is anywhere rule.
    if (tc.production().klabel().filter(k -> k.head().equals(KLabels.KREWRITE)).isDefined()) {
      Term lhs = stripBrackets(tc.get(0));
      if (lhs instanceof Ambiguity) {
        throw new AssertionError("Ambiguities are not yet supported!");
      }
      ProductionReference lhsPr = (ProductionReference) lhs;
      return isAnywhere
          || lhsPr.production().att().contains(Att.FUNCTION())
          || lhsPr.production().att().getMacro().isDefined();
    }
    return false;
  }

  /**
   * The main entry point of SortInferencer, inferring the sort of the input's variables and
   * recording the results by inserting casts.
   *
   * @param t - The Term to infer the sort of
   * @param topSort - The expected sort of t
   * @param isAnywhere - Whether t is a rule with an attribute indicating that the rule applies
   *     anywhere in a configuration (e.g. macro, simplification, anywhere, ...).
   * @return If t is not well-sorted, then a set of errors. If t is well-sorted, then a new Term
   *     which is the same as t, but with each variable wrapped in a SemanticCast to its inferred
   *     type (returning an Ambiguity of all solutions when there are multiple possible sorts).
   */
  public Either<Set<KEMException>, Term> apply(Term t, Sort topSort, boolean isAnywhere) {
    Set<TermSort<Sort>> monoRes;
    try {
      InferenceDriver driver = new InferenceDriver(mod.subsorts());
      BoundedSort itemSort = infer(t, isAnywhereRule(t, isAnywhere), driver);
      BoundedSort topBoundedSort = driver.sortToBoundedSort(topSort, null);
      driver.constrain(itemSort, topBoundedSort, (ProductionReference) t);
      TermSort<BoundedSort> unsimplifiedRes = driver.getResult(t, topBoundedSort);
      TermSort<CompactSort> res = simplify(unsimplifiedRes.mapSorts(CompactSort::makeCompact));
      monoRes = monomorphize(res);
    } catch (SortInferenceError e) {
      Set<KEMException> errs = new HashSet<>();
      errs.add(e.asInnerParseError(t));
      return Left.apply(errs);
    }

    Set<Term> items = new HashSet<>();
    for (TermSort<Sort> mono : monoRes) {
      items.add(insertCasts(t, mono, false));
    }
    if (items.size() == 1) {
      return Right.apply(items.iterator().next());
    } else {
      return Right.apply(Ambiguity.apply(items));
    }
  }

  /**
   * Infer an unsimplified BoundedSort for a term.
   *
   * @param t - The term we want to infer the type of
   * @param isAnywhereRule - Whether t is a rule which can be applied anywhere in a configuration
   * @param driver - A driver maintaining all state during inference, including the sort of all
   *     variables as they are encountered.
   * @return The unsimplified sort of the input term
   * @throws SortInferenceError - an exception indicating that the term is not well-typed
   */
  private BoundedSort infer(Term t, boolean isAnywhereRule, InferenceDriver driver)
      throws SortInferenceError {
    if (t instanceof Ambiguity) {
      throw new AssertionError("Ambiguities are not yet supported!");
    }

    ProductionReference pr = (ProductionReference) t;
    if (pr instanceof Constant c) {
      if (c.production().sort().equals(Sorts.KVariable())
          || c.production().sort().equals(Sorts.KConfigVar())) {
        return driver.varSort(c);
      }
      return driver.sortToBoundedSort(c.production().sort(), pr);
    }

    TermCons tc = (TermCons) pr;
    if (isAnywhereRule
        && tc.production().klabel().filter(k -> k.head().equals(KLabels.KREWRITE)).isDefined()) {
      BoundedSort lhsSort = infer(tc.get(0), false, driver);
      // To prevent widening, we constrain RHS's inferred sort <: LHS's declared sort.
      //
      // Note that we do actually need the LHS's declared sort. The LHS's inferred sort
      // is a variable X with a bound L <: X, and constraining against X would just add a
      // new lower bound aka permit widening.
      //
      // It's also safe to assume the LHS is not an Ambiguity due to PushTopAmbiguitiesUp
      ProductionReference lhsDeclaredPr = (ProductionReference) stripBrackets(tc.get(0));
      BoundedSort lhsDeclaredSort =
          driver.sortToBoundedSort(lhsDeclaredPr.production().sort(), lhsDeclaredPr);
      BoundedSort rhsSort = infer(tc.get(1), false, driver);
      driver.constrain(rhsSort, lhsDeclaredSort, (ProductionReference) tc.get(1));

      // Handle usual production constraints
      BoundedSort rewriteParam = driver.sortToBoundedSort(tc.production().sort(), tc);
      driver.constrain(lhsSort, rewriteParam, tc);
      driver.constrain(rhsSort, rewriteParam, tc);
      return driver.returnSort(tc);
    }

    if (tc.production()
        .klabel()
        .filter(k -> k.name().equals("#SyntacticCast") || k.name().equals("#SyntacticCastBraced"))
        .isDefined()) {
      BoundedSort castedSort = driver.sortToBoundedSort(tc.production().sort(), tc);
      BoundedSort childSort = infer(tc.get(0), isAnywhereRule, driver);
      driver.constrain(castedSort, childSort, tc);
      driver.constrain(childSort, castedSort, tc);
      return driver.returnSort(tc);
    }

    for (int prodI = 0, tcI = 0; prodI < tc.production().items().size(); prodI++) {
      if (!(tc.production().items().apply(prodI) instanceof NonTerminal nt)) {
        continue;
      }
      BoundedSort expectedSort = driver.sortToBoundedSort(nt.sort(), tc);
      BoundedSort childSort = infer(tc.get(tcI), isAnywhereRule, driver);
      driver.constrain(childSort, expectedSort, tc);
      tcI++;
    }
    return driver.returnSort(tc);
  }

  /**
   * Perform co-occurrence analysis to remove redundant type variables and unify those that are
   * indistinguishable.
   */
  private TermSort<CompactSort> simplify(TermSort<CompactSort> res) {
    Map<Tuple2<SortVariable, Boolean>, CoOccurrences> coOccurrences =
        analyzeCoOccurrences(res, CoOccurMode.ALWAYS);
    Map<SortVariable, Optional<CompactSort>> varSubst = new HashMap<>();
    // Simplify away all those variables that only occur in negative (resp. positive) position.
    Set<SortVariable> allVars =
        coOccurrences.keySet().stream().map(Tuple2::_1).collect(Collectors.toSet());
    allVars.forEach(
        (v) -> {
          boolean negative = coOccurrences.containsKey(Tuple2.apply(v, false));
          boolean positive = coOccurrences.containsKey(Tuple2.apply(v, true));
          if ((negative && !positive) || (!negative && positive)) {
            varSubst.put(v, Optional.empty());
          }
        });

    List<Boolean> pols = new ArrayList<>();
    pols.add(false);
    pols.add(true);

    for (SortVariable v : allVars) {
      if (varSubst.containsKey(v)) {
        continue;
      }
      for (Boolean pol : pols) {
        if (!coOccurrences.containsKey(Tuple2.apply(v, pol))) {
          continue;
        }
        CoOccurrences vCoOccurs = coOccurrences.get(Tuple2.apply(v, pol));
        // v is not in varSubst already, so it must occur in both polarities
        // thus this access is valid
        CoOccurrences vOpCoOccurs = coOccurrences.get(Tuple2.apply(v, !pol));
        for (SortVariable w : vCoOccurs.vars()) {
          if (v.equals(w) || varSubst.containsKey(w)) {
            continue;
          }
          if (coOccurrences.containsKey(Tuple2.apply(w, pol))
              && coOccurrences.get(Tuple2.apply(w, pol)).vars().contains(v)) {
            // v and w always co-occur in the given polarity, so we unify w into v
            varSubst.put(w, Optional.of(new CompactSort(v)));
            // we also need to update v's co-occurrences correspondingly
            // (intersecting with w's)
            CoOccurrences wOpCoOccurs = coOccurrences.get(Tuple2.apply(w, !pol));
            vOpCoOccurs.vars().retainAll(wOpCoOccurs.vars());
            vOpCoOccurs.ctors().retainAll(wOpCoOccurs.ctors());
            vOpCoOccurs.vars().add(v);
          }
        }
        for (SortHead ctor : vCoOccurs.ctors()) {
          // This is not a variable, so check if we have a sandwich ctor <: v <: ctor
          // and can thus simplify away v
          if (vOpCoOccurs.ctors().contains(ctor)) {
            varSubst.put(v, Optional.empty());
          }
        }
      }
    }

    return res.mapSorts((c, p) -> c.substitute(varSubst));
  }

  /**
   * Modes for the co-occurrence analysis. A variable is said to co-occur positively (resp.
   * negatively) with another type if they occur in the same type union (resp. intersection).
   */
  private enum CoOccurMode {
    /**
     * For each variable and polarity, record only those sorts which always co-occur with the in
     * every single position. This is the co-occurrence analysis described in SimpleSub.
     */
    ALWAYS,
    /**
     * For each variable and polarity, record any sort that ever co-occurs with the variable in at
     * least one position. In effect, this records all the bounds on the given variable.
     */
    EVER
  }

  private record CoOccurrences(Set<SortVariable> vars, Set<SortHead> ctors) {}

  /**
   * Compute the co-occurrences within a TermSort based on the given mode.
   *
   * @param res - The TermSort to analyze
   * @param mode - Mode indicating what type of analysis to perform. See documentation for the
   *     CoOccurMode enum above.
   * @return The result of the co-occurrence analysis.
   */
  private Map<Tuple2<SortVariable, Boolean>, CoOccurrences> analyzeCoOccurrences(
      TermSort<CompactSort> res, CoOccurMode mode) {
    Map<Tuple2<SortVariable, Boolean>, CoOccurrences> coOccurrences = new HashMap<>();
    res.forEachSort((s, pol) -> updateCoOccurrences(s, pol, mode, coOccurrences));
    return coOccurrences;
  }

  /**
   * Update the co-occurrence analysis results so-far to account for the occurrences within sort
   *
   * @param sort - The sort which we are processing
   * @param polarity - The polarity of the provided sort
   * @param coOccurrences - mutated to record all co-occurrences for each variable occurring in sort
   */
  private void updateCoOccurrences(
      CompactSort sort,
      boolean polarity,
      CoOccurMode mode,
      Map<Tuple2<SortVariable, Boolean>, CoOccurrences> coOccurrences) {
    for (SortVariable var : sort.vars()) {
      Tuple2<SortVariable, Boolean> polVar = Tuple2.apply(var, polarity);
      if (coOccurrences.containsKey(polVar)) {
        CoOccurrences coOccurs = coOccurrences.get(polVar);
        switch (mode) {
          case ALWAYS -> {
            coOccurs.vars().retainAll(sort.vars());
            coOccurs.ctors().retainAll(sort.ctors());
          }
          case EVER -> {
            coOccurs.vars().addAll(sort.vars());
            coOccurs.ctors().addAll(sort.ctors());
          }
        }
      } else {
        coOccurrences.put(
            polVar, new CoOccurrences(new HashSet<>(sort.vars()), new HashSet<>(sort.ctors())));
      }
    }
  }

  /**
   * Monomorphize a TermSort.
   *
   * @param res - The result to monomorphize
   * @return A set of all possible monomorphizations of the input result
   * @throws SortInferenceError - An error if there are no monomorphizations which can actually be
   *     produced from the subsort lattice.
   */
  private Set<TermSort<Sort>> monomorphize(TermSort<CompactSort> res) throws SortInferenceError {
    Map<Tuple2<SortVariable, Boolean>, CoOccurrences> bounds =
        analyzeCoOccurrences(res, CoOccurMode.EVER);

    // Produce all valid instantiations by monomorphizing one variable at a time
    Set<SortVariable> allVars =
        bounds.keySet().stream().map(Tuple2::_1).collect(Collectors.toSet());
    Set<Map<SortVariable, Sort>> instantiations = new HashSet<>();
    instantiations.add(new HashMap<>());
    for (SortVariable var : allVars) {
      Set<Map<SortVariable, Sort>> newInstantiations = new HashSet<>();
      for (Map<SortVariable, Sort> instant : instantiations) {
        newInstantiations.addAll(monomorphizeInVar(instant, var, bounds));
      }
      if (newInstantiations.isEmpty()) {
        throw new MonomorphizationError(res.term());
      }
      instantiations = newInstantiations;
    }

    Set<TermSort<Sort>> monos = new HashSet<>();
    SortInferenceError lastError = null;
    for (Map<SortVariable, Sort> inst : instantiations) {
      Either<SortInferenceError, TermSort<Sort>> monoRes = realizeTermSort(res, inst);
      if (monoRes.isLeft()) {
        lastError = monoRes.left().get();
      } else {
        monos.add(monoRes.right().get());
      }
    }
    if (monos.isEmpty()) {
      assert lastError != null;
      throw lastError;
    }
    return monos;
  }

  /**
   * Update the instantiation of variables so far to also include all possible instantiations of the
   * provided sort variable.
   *
   * @param instantiation - A particular instantiation for some subset of the SortVariables
   *     occurring in our term.
   * @param var - A SortVariable that we wish to add to our instantiation
   * @param bounds - A map of entries (v, p) |-> C where C records every sort that ever co-occurs
   *     with the Variable v in the polarity p in our term.
   * @return A set of all possible new instantiations accounting for var
   */
  private Set<Map<SortVariable, Sort>> monomorphizeInVar(
      Map<SortVariable, Sort> instantiation,
      SortVariable var,
      Map<Tuple2<SortVariable, Boolean>, CoOccurrences> bounds) {

    // Record the bounds in each polarity, then search the subsort poset for all solutions
    // that satisfy these bounds
    Map<Boolean, Set<Sort>> polBounds = new HashMap<>();
    polBounds.put(true, new HashSet<>());
    polBounds.put(false, new HashSet<>());

    for (Entry<Boolean, Set<Sort>> polBound : polBounds.entrySet()) {
      Tuple2<SortVariable, Boolean> polVar = Tuple2.apply(var, polBound.getKey());
      if (!bounds.containsKey(polVar)) {
        continue;
      }
      CoOccurrences bound = bounds.get(polVar);
      for (SortVariable bVar : bound.vars()) {
        // If bVar hasn't been instantiated yet, we can simply ignore it. If any instantiation we
        // produce here is invalid when considering bVar, we will prune it later when bVar
        // is actually instantiated.
        if (instantiation.containsKey(bVar)) {
          polBound.getValue().add(instantiation.get(bVar));
        }
      }
      for (SortHead bCtor : bound.ctors()) {
        polBound.getValue().add(new org.kframework.kore.ADT.Sort(bCtor.name(), Seq()));
      }
    }

    Set<Sort> range = mod.subsorts().upperBounds(polBounds.get(true));
    range.retainAll(mod.subsorts().lowerBounds(polBounds.get(false)));

    Set<Map<SortVariable, Sort>> insts = new HashSet<>();
    for (Sort sort : range) {
      Map<SortVariable, Sort> inst = new HashMap<>(instantiation);
      inst.put(var, sort);
      insts.add(inst);
    }
    return insts;
  }

  /**
   * Apply an instantiation to a {@code TermSort<CompactSort>}, then compute type joins/meets to
   * collapse it to a {@code TermSort<Sort>}.
   *
   * @param res - The provided TermSort to realize
   * @param instantiation - A concrete value for each variable occurring in res
   * @return An equivalent {@code TermSort<Sort>}
   */
  private Either<SortInferenceError, TermSort<Sort>> realizeTermSort(
      TermSort<CompactSort> res, Map<SortVariable, Sort> instantiation) {
    Either<CompactSort.LatticeOpError, Sort> sortRes =
        res.sort().asSort(true, instantiation, mod.subsorts());
    if (sortRes.isLeft()) {
      return Left.apply(new LatticeOpError(sortRes.left().get(), res.term(), Optional.empty()));
    }
    Sort sort = sortRes.right().get();
    Map<VariableId, Sort> varSorts = new HashMap<>();
    for (Entry<VariableId, ? extends CompactSort> entry : res.varSorts().entrySet()) {
      Either<CompactSort.LatticeOpError, Sort> varRes =
          entry.getValue().asSort(false, instantiation, mod.subsorts());
      if (varRes.isLeft()) {
        CompactSort.LatticeOpError latticeErr = varRes.left().get();
        if (entry.getKey() instanceof VariableId.Anon anon) {
          return Left.apply(
              new LatticeOpError(latticeErr, anon.constant(), Optional.of("variable")));
        }
        if (entry.getKey() instanceof VariableId.Named named) {
          return Left.apply(
              new LatticeOpError(latticeErr, res.term(), Optional.of("variable " + named.name())));
        }
        throw new AssertionError("VariableId should be either Anon or Named");
      }
      varSorts.put(entry.getKey(), varRes.right().get());
    }
    return Right.apply(new TermSort<>(res.term(), sort, varSorts));
  }

  /**
   * Insert SemanticCasts around each variable casting it to the appropriate Sort.
   *
   * @param t - The term to insert casts on
   * @param sorts - The inferred sorts of t
   * @param existingCast - Whether t is already wrapped in an existing cast
   */
  private Term insertCasts(Term t, TermSort<Sort> sorts, boolean existingCast) {
    if (t instanceof Ambiguity) {
      throw new AssertionError("Ambiguities are not yet supported!");
    }

    ProductionReference pr = (ProductionReference) t;
    if (pr instanceof Constant c) {
      if (c.production().sort().equals(Sorts.KVariable())
          || c.production().sort().equals(Sorts.KConfigVar())) {
        Sort inferred = sorts.varSorts().get(VariableId.apply(c));
        if (!existingCast) {
          Production cast =
              mod.productionsFor().apply(KLabel("#SemanticCastTo" + inferred.toString())).head();
          return TermCons.apply(ConsPStack.singleton(t), cast, t.location(), t.source());
        }
      }
      return c;
    }

    TermCons tc = (TermCons) pr;
    boolean isCast =
        tc.production().klabel().filter(k -> k.name().startsWith("#SemanticCastTo")).isDefined();
    for (int i = 0; i < tc.items().size(); i++) {
      tc = tc.with(i, insertCasts(tc.get(i), sorts, isCast));
    }
    return tc;
  }

  private static Term stripBrackets(Term tc) {
    Term child = tc;
    while (child instanceof TermCons
        && ((TermCons) child).production().att().contains(Att.BRACKET())) {
      child = ((TermCons) child).get(0);
    }
    return child;
  }
}

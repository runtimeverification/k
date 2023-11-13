package org.kframework.parser.inner.disambiguation;

import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.BoundedSort;
import org.kframework.parser.CompactSort;
import org.kframework.parser.Constant;
import org.kframework.parser.InferenceResult;
import org.kframework.parser.InferenceState;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

/**
 * Disambiguation transformer which performs type checking and infers the sorts of variables.
 *
 * <p>The overall design is based on the algorithm described in "The Simple Essence of Algebraic
 * Subtyping: Principal Type Inference with Subtyping Made Easy" by Lionel Parreaux.
 *
 * <p>Specifically, we can straightforwardly treat any (non-ambiguous) term in our language as a
 * function in the SimpleSub
 *
 * <p>- Constants are treated as built-ins - TermCons are treated as primitive functions
 */
public class SortInferencer {
  private final Module mod;

  private int id = 0;

  private final Map<ProductionReference, Integer> prIds = new HashMap<>();

  private final PrintWriter debug;

  /**
   * Modes controlling how type inference inserts semantic (x:Sort) or strict (x::Sort) casts on
   * variables in order to record their inferred types.
   */
  public enum CastInsertionMode {
    /**
     * Don't insert any casts. Type inference is still run and will report an error if the term is
     * ill-typed, but it never modifies the term.
     *
     * <ul>
     *   <li>x -> x
     *   <li>x:Sort -> x:Sort
     *   <li>x::Sort -> x::Sort
     * </ul>
     */
    NONE,
    /**
     * Insert a semantic cast on every variable not currently wrapped by one.
     *
     * <ul>
     *   <li>x -> x:Sort
     *   <li>x:Sort -> x:Sort
     *   <li>x::Sort -> (x:Sort)::Sort
     * </ul>
     */
    SEMANTIC_CASTS_ON_ALL_VARS,
    /**
     * Insert a strict cast on every variable not currently wrapped by either a strict cast or a
     * semantic cast.
     *
     * <ul>
     *   <li>x -> x::Sort
     *   <li>x:Sort -> x:Sort
     *   <li>x::Sort -> x::Sort
     * </ul>
     */
    STRICT_CASTS_ON_UNCASTED_VARS,
  }

  private final CastInsertionMode castMode;

  public SortInferencer(Module mod, PrintWriter debug, CastInsertionMode castMode) {
    this.mod = mod;
    this.debug = debug;
    this.castMode = castMode;
  }

  /**
   * @param t - A term
   * @return Whether t is a Term which the sort inference engine can currently handle. Specifically,
   */
  public static boolean isSupported(Term t) {
    return !hasAmbiguity(t) && !hasStrictCast(t) && !hasParametricSorts(t);
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

  private static boolean hasStrictCast(Term t) {
    if (t instanceof Ambiguity) {
      return ((Ambiguity) t).items().stream().anyMatch(SortInferencer::hasStrictCast);
    }
    ProductionReference pr = (ProductionReference) t;
    if (pr.production().klabel().isDefined()) {
      KLabel klabel = pr.production().klabel().get();
      String label = klabel.name();
      if (label.equals("#SyntacticCast") || label.equals("#InnerCast")) {
        return true;
      }
    }
    if (t instanceof Constant) {
      return false;
    }
    return ((TermCons) t).items().stream().anyMatch(SortInferencer::hasStrictCast);
  }

  private static boolean hasParametricSorts(Term t) {
    if (t instanceof Ambiguity) {
      return ((Ambiguity) t).items().stream().anyMatch(SortInferencer::hasParametricSorts);
    }
    ProductionReference pr = (ProductionReference) t;
    if (stream(pr.production().items())
        .filter(pi -> pi instanceof NonTerminal)
        .map(pi -> ((NonTerminal) pi).sort())
        .anyMatch(s -> !s.params().isEmpty())) {
      return true;
    }
    if (pr instanceof Constant) {
      return false;
    }
    return ((TermCons) t).items().stream().anyMatch(SortInferencer::hasParametricSorts);
  }

  public Either<Set<KEMException>, Term> apply(Term t, Sort topSort, boolean isAnywhereRule) {
    t.source().ifPresent(debug::println);
    t.location().ifPresent(debug::println);

    Set<InferenceResult<Sort>> monoRes;
    try {
      InferenceState inferState =
          new InferenceState(new HashMap<>(), new HashMap<>(), new HashSet<>());
      BoundedSort itemSort = infer(t, isAnywhereRule, inferState);
      BoundedSort topBoundedSort = sortWithoutSortVariablesToBoundedSort(topSort);
      constrain(itemSort, topBoundedSort, inferState, (ProductionReference) t);
      InferenceResult<BoundedSort> unsimplifiedRes =
          new InferenceResult<>(topBoundedSort, inferState.varSorts());
      InferenceResult<CompactSort> res = simplify(compact(unsimplifiedRes));
      monoRes = monomorphize(res);
    } catch (SortInferenceError e) {
      Set<KEMException> errs = new HashSet<>();
      errs.add(e.asInnerParseError());
      return Left.apply(errs);
    }

    if (castMode == CastInsertionMode.NONE) {
      return Right.apply(t);
    }

    Set<Term> items = new HashSet<>();
    for (InferenceResult<Sort> mono : monoRes) {
      items.add(insertCasts(t, mono, CastContext.NONE));
    }
    if (items.size() == 1) {
      return Right.apply(items.iterator().next());
    } else {
      return Right.apply(Ambiguity.apply(items));
    }
  }

  private static class SortInferenceError extends Exception {
    private final Optional<ProductionReference> pr;

    SortInferenceError(String message, Optional<ProductionReference> pr) {
      super(message);
      this.pr = pr;
    }

    public KEMException asInnerParseError() {
      return pr.map(p -> KEMException.innerParserError(getMessage(), p))
          .orElseGet(() -> KEMException.innerParserError(getMessage()));
    }

    private static SortInferenceError constrainError(Sort lhs, Sort rhs, ProductionReference pr) {
      String msg;
      if (pr instanceof Constant) {
        msg =
            "Unexpected sort "
                + lhs
                + " for term "
                + ((Constant) pr).value()
                + ". Expected "
                + rhs
                + ".";
      } else {
        msg =
            "Unexpected sort "
                + lhs
                + " for term parsed as production "
                + pr.production()
                + ". Expected "
                + rhs
                + ".";
      }
      return new SortInferenceError(msg, Optional.of(pr));
    }

    private static SortInferenceError boundsError(
        Set<Sort> sorts, Set<Sort> candidates, boolean polarity) {
      String msg =
          "Could not compute "
              + (polarity ? "least upper bound" : "greatest lower bound")
              + " of sorts "
              + sorts
              + ". ";
      if (candidates.isEmpty()) {
        msg += "No possible candidates.";
      } else {
        msg += "Multiple possible candidates: " + candidates + ".";
      }
      return new SortInferenceError(msg, Optional.empty());
    }
  }

  /**
   * @param t - The term we want to infer the type of
   * @param isAnywhereRule - Whether t is an anywhere rule
   * @param inferState - All state maintained during inference, which will be updated throughout
   *     with sorts for all contained variables
   * @return The unsimplified sort of the input term
   * @throws SortInferenceError - an exception indicating that the term is not well-typed
   */
  private BoundedSort infer(Term t, boolean isAnywhereRule, InferenceState inferState)
      throws SortInferenceError {
    if (t instanceof Ambiguity) {
      throw new AssertionError("Ambiguities are not yet supported!");
    }

    ProductionReference pr = (ProductionReference) t;
    if (!prIds.containsKey(pr)) {
      prIds.put(pr, id);
      id++;
    }
    addParamsFromProduction(inferState, pr);

    if (pr instanceof Constant c) {
      if (c.production().sort().equals(Sorts.KVariable())
          || c.production().sort().equals(Sorts.KConfigVar())) {
        String name = varName(c);
        if (!inferState.varSorts().containsKey(name)) {
          inferState
              .varSorts()
              .put(
                  name,
                  new BoundedSort.Variable(
                      new ArrayList<>(), new ArrayList<>(), Optional.of(name)));
        }
        return inferState.varSorts().get(name);
      }
      return sortToBoundedSort(c.production().sort(), pr, inferState.params());
    }

    TermCons tc = (TermCons) pr;
    if (tc.production().klabel().isDefined()) {
      KLabel klabel = tc.production().klabel().get();
      String label = klabel.name();
      if (label.equals("#SyntacticCast") || label.equals("#InnerCast")) {
        throw new AssertionError("Strict casts not yet supported!");
      }

      // For function, macro, and anywhere rules, the RHS must be a subsort of the LHS
      if (klabel.head().equals(KLabels.KREWRITE)) {
        if (isAnywhereRule || isFunctionOrMacro(tc.get(0))) {
          BoundedSort lhsSort = infer(tc.get(0), isAnywhereRule, inferState);
          BoundedSort rhsSort = infer(tc.get(1), isAnywhereRule, inferState);
          constrain(rhsSort, lhsSort, inferState, pr);
          return lhsSort;
        }
      }
    }

    for (int prodI = 0, tcI = 0; prodI < tc.production().items().size(); prodI++) {
      if (!(tc.production().items().apply(prodI) instanceof NonTerminal nt)) {
        continue;
      }
      BoundedSort expectedSort = sortToBoundedSort(nt.sort(), pr, inferState.params());
      BoundedSort childSort = infer(tc.get(tcI), isAnywhereRule, inferState);
      constrain(childSort, expectedSort, inferState, pr);
      tcI++;
    }
    BoundedSort resSort =
        new BoundedSort.Variable(new ArrayList<>(), new ArrayList<>(), Optional.empty());
    constrain(
        sortToBoundedSort(tc.production().sort(), pr, inferState.params()),
        resSort,
        inferState,
        pr);
    return resSort;
  }

  private static boolean isFunctionOrMacro(Term tc) {
    Term raw = stripBrackets(tc);
    if (raw instanceof ProductionReference pr) {
      return pr.production().att().contains(Att.FUNCTION())
          || ExpandMacros.isMacro(pr.production());
    }
    return false;
  }

  private void addParamsFromProduction(InferenceState inferState, ProductionReference pr) {
    for (Sort param : iterable(pr.production().params())) {
      inferState
          .params()
          .put(
              Tuple2.apply(pr, param),
              new BoundedSort.Variable(
                  new ArrayList<>(), new ArrayList<>(), Optional.of(paramName(pr, param))));
    }
  }

  private void constrain(
      BoundedSort lhs, BoundedSort rhs, InferenceState inferState, ProductionReference pr)
      throws SortInferenceError {
    if (lhs.equals(rhs) || inferState.constraintCache().contains(Tuple2.apply(lhs, rhs))) {
      return;
    }

    if (lhs instanceof BoundedSort.Variable lhsVar) {
      inferState.constraintCache().add(Tuple2.apply(lhs, rhs));
      lhsVar.upperBounds().add(rhs);
      for (BoundedSort lhsLower : lhsVar.lowerBounds()) {
        constrain(lhsLower, rhs, inferState, pr);
      }
      return;
    }

    if (rhs instanceof BoundedSort.Variable rhsVar) {
      inferState.constraintCache().add(Tuple2.apply(lhs, rhs));
      rhsVar.lowerBounds().add(lhs);
      for (BoundedSort rhsUpper : rhsVar.upperBounds()) {
        constrain(lhs, rhsUpper, inferState, pr);
      }
      return;
    }

    // If they are primitive sorts, we can directly check the sort poset directly
    BoundedSort.Constructor lhsCtor = (BoundedSort.Constructor) lhs;
    BoundedSort.Constructor rhsCtor = (BoundedSort.Constructor) rhs;
    if (lhsCtor.head().params() == 0 && rhsCtor.head().params() == 0) {
      Sort lhsSort = new org.kframework.kore.ADT.Sort(lhsCtor.head().name(), Seq());
      Sort rhsSort = new org.kframework.kore.ADT.Sort(rhsCtor.head().name(), Seq());
      if (mod.subsorts().lessThanEq(lhsSort, rhsSort)) {
        return;
      }
      throw SortInferenceError.constrainError(lhsSort, rhsSort, pr);
    }

    throw new AssertionError("Parametric sorts are not yet supported!");
  }

  private CompactSort compact(BoundedSort sort, boolean polarity) {
    if (sort instanceof BoundedSort.Constructor ctor) {
      if (ctor.head().params() == 0) {
        Set<SortHead> ctors = new HashSet<>();
        ctors.add(ctor.head());
        return new CompactSort(new HashSet<>(), ctors);
      }
      throw new AssertionError("Parametric sorts are not yet supported!");
    }
    BoundedSort.Variable var = (BoundedSort.Variable) sort;
    List<BoundedSort> bounds = polarity ? var.lowerBounds() : var.upperBounds();

    Set<BoundedSort.Variable> vars = new HashSet<>();
    Set<SortHead> ctors = new HashSet<>();
    vars.add(var);
    for (BoundedSort bound : bounds) {
      CompactSort compactBound = compact(bound, polarity);
      vars.addAll(compactBound.vars());
      ctors.addAll(compactBound.ctors());
    }
    return new CompactSort(vars, ctors);
  }

  private InferenceResult<CompactSort> compact(InferenceResult<BoundedSort> res) {
    CompactSort sort = compact(res.sort(), true);

    Map<String, CompactSort> varSorts = new HashMap<>();
    for (Map.Entry<String, BoundedSort> entry : res.varSorts().entrySet()) {
      varSorts.put(entry.getKey(), compact(entry.getValue(), false));
    }

    return new InferenceResult<>(sort, varSorts);
  }

  private InferenceResult<CompactSort> simplify(InferenceResult<CompactSort> res)
      throws SortInferenceError {

    Map<Tuple2<BoundedSort.Variable, Boolean>, Set<BoundedSort>> coOccurrences =
        analyzeCoOcurrences(res, CoOccurMode.ALWAYS);
    Map<BoundedSort.Variable, Optional<BoundedSort.Variable>> varSubst = new HashMap<>();
    // Simplify away all those variables that only occur in negative (resp. positive) position.
    Set<BoundedSort.Variable> allVars =
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

    for (Boolean pol : pols) {
      for (BoundedSort.Variable v : allVars) {
        for (BoundedSort co : coOccurrences.getOrDefault(Tuple2.apply(v, pol), new HashSet<>())) {
          if (co instanceof BoundedSort.Variable w) {
            if (v.equals(w) || varSubst.containsKey(w)) {
              continue;
            }
            if (coOccurrences.getOrDefault(Tuple2.apply(w, pol), new HashSet<>()).contains(v)) {
              // v and w co-occur in the given polarity, so we unify w into v
              varSubst.put(w, Optional.of(v));
              // we also need to update v's co-occurrences correspondingly
              // (intersecting with w's)
              coOccurrences
                  .get(Tuple2.apply(v, !pol))
                  .retainAll(coOccurrences.get(Tuple2.apply(w, !pol)));
              coOccurrences.get(Tuple2.apply(v, !pol)).add(v);
            }
            continue;
          }
          // This is not a variable, so check if we have a sandwich co <: v <: co
          // and can thus simplify away v
          if (coOccurrences.getOrDefault(Tuple2.apply(v, !pol), new HashSet<>()).contains(co)) {
            varSubst.put(v, Optional.empty());
          }
        }
      }
    }

    CompactSort newSort = applySubstitutions(res.sort(), varSubst);
    Map<String, CompactSort> newVarSorts =
        res.varSorts().entrySet().stream()
            .collect(
                Collectors.toMap(
                    (Entry::getKey), (e) -> applySubstitutions(e.getValue(), varSubst)));
    return new InferenceResult<>(newSort, newVarSorts);
  }

  /** Modes for the co-occurrence analysis. */
  private enum CoOccurMode {
    /** Record only those sorts which always co-occur with a given variable and polarity. */
    ALWAYS,
    /** Record any sort that ever co-occurs with a given variable and polarity. */
    EVER
  }

  private Map<Tuple2<BoundedSort.Variable, Boolean>, Set<BoundedSort>> analyzeCoOcurrences(
      InferenceResult<CompactSort> res, CoOccurMode mode) {
    Map<Tuple2<BoundedSort.Variable, Boolean>, Set<BoundedSort>> coOccurrences = new HashMap<>();

    // Boolean is used to represent polarity - true is positive, false is negative
    List<Tuple2<CompactSort, Boolean>> compactSorts = new ArrayList<>();
    // The sort of the overall term is positive
    compactSorts.add(Tuple2.apply(res.sort(), true));
    // The sorts of variables are negative
    compactSorts.addAll(
        res.varSorts().values().stream().map((v) -> Tuple2.apply(v, false)).toList());
    compactSorts.forEach(
        polSort -> updateCoOccurrences(polSort._1, polSort._2, mode, coOccurrences));

    return coOccurrences;
  }

  /**
   * Update the co-occurrence analysis results so-far to account for the occurrences within sort
   *
   * @param sort - The sort which we are processing
   * @param polarity - The polarity of the provided sort
   * @param coOccurrences - mutated to record all co-occurrences in each variable occurring in sort
   */
  private void updateCoOccurrences(
      CompactSort sort,
      boolean polarity,
      CoOccurMode mode,
      Map<Tuple2<BoundedSort.Variable, Boolean>, Set<BoundedSort>> coOccurrences) {
    for (BoundedSort.Variable var : sort.vars()) {
      Set<BoundedSort> newOccurs =
          Stream.concat(
                  sort.vars().stream().map(v -> (BoundedSort) v),
                  sort.ctors().stream().map(BoundedSort.Constructor::new))
              .collect(Collectors.toSet());
      Tuple2<BoundedSort.Variable, Boolean> polVar = Tuple2.apply(var, polarity);
      if (coOccurrences.containsKey(polVar)) {
        switch (mode) {
          case ALWAYS -> coOccurrences.get(polVar).retainAll(newOccurs);
          case EVER -> coOccurrences.get(polVar).addAll(newOccurs);
        }
      } else {
        coOccurrences.put(polVar, newOccurs);
      }
    }
  }

  /**
   * Apply a substitution to a sort
   *
   * @param sort - The input sort
   * @param varSubst - A map describing the substitution - a -> None indicates that a should be
   *     removed form the sort - a -> Some(b) indicates that a should be replaced by b
   * @return sort with the substitution applied
   */
  private static CompactSort applySubstitutions(
      CompactSort sort, Map<BoundedSort.Variable, Optional<BoundedSort.Variable>> varSubst) {
    Set<BoundedSort.Variable> vars = new HashSet<>();
    for (BoundedSort.Variable var : sort.vars()) {
      if (!varSubst.containsKey(var)) {
        vars.add(var);
        continue;
      }
      varSubst.get(var).ifPresent(vars::add);
    }
    Set<SortHead> ctors = new HashSet<>(sort.ctors());
    return new CompactSort(vars, ctors);
  }

  //  private CompactSort computeTypes(CompactSort sort, boolean polarity) throws SortInferenceError
  // {
  //    if (sort.ctors().stream().anyMatch(p -> p.params() != 0)) {
  //      throw new AssertionError("Parametric sorts are not yet supported!");
  //    }
  //    if (sort.ctors().size() <= 1) {
  //      return new CompactSort(new HashSet<>(sort.vars()), new HashSet<>(sort.ctors()));
  //    }
  //    Set<Sort> sorts = sort.ctors().stream().map(KORE::Sort).collect(Collectors.toSet());
  //    Set<Sort> ogBounds =
  //        polarity ? mod.subsorts().upperBounds(sorts) : mod.subsorts().lowerBounds(sorts);
  //    Set<Sort> bounds = new HashSet<>(ogBounds);
  //    // TODO: bounds.removeIf(s -> mod.subsorts().lessThanEq(s, Sorts.KBott()) ||
  //    // mod.subsorts().greaterThan(s, Sorts.K()));
  //    Set<Sort> res = polarity ? mod.subsorts().minimal(bounds) : mod.subsorts().maximal(bounds);
  //
  //    if (res.size() != 1) {
  //      throw SortInferenceError.boundsError(sorts, res, polarity);
  //    }
  //
  //    Set<SortHead> newCtors = res.stream().map(Sort::head).collect(Collectors.toSet());
  //
  //    return new CompactSort(new HashSet<>(sort.vars()), newCtors);
  //  }

  private Set<InferenceResult<Sort>> monomorphize(InferenceResult<CompactSort> res)
      throws SortInferenceError {
    Map<Tuple2<BoundedSort.Variable, Boolean>, Set<BoundedSort>> bounds =
        analyzeCoOcurrences(res, CoOccurMode.EVER);
    Set<BoundedSort.Variable> allVars =
        bounds.keySet().stream().map(Tuple2::_1).collect(Collectors.toSet());
    Set<Map<BoundedSort.Variable, Sort>> instantiations = new HashSet<>();
    instantiations.add(new HashMap<>());
    for (BoundedSort.Variable var : allVars) {
      Set<Map<BoundedSort.Variable, Sort>> newInstantiations = new HashSet<>();
      for (Map<BoundedSort.Variable, Sort> instant : instantiations) {
        newInstantiations.addAll(monomorphizeInVar(instant, var, bounds));
      }
      // TODO: Throw a nice error message here
      assert !newInstantiations.isEmpty();
      instantiations = newInstantiations;
    }

    Set<InferenceResult<Sort>> monos = new HashSet<>();
    SortInferenceError lastError = null;
    for (Map<BoundedSort.Variable, Sort> inst : instantiations) {
      try {
        Sort sort = compactSortToSort(res.sort(), true, inst);
        Map<String, Sort> varSorts = new HashMap<>();
        for (Entry<String, CompactSort> entry : res.varSorts().entrySet()) {
          varSorts.put(entry.getKey(), compactSortToSort(entry.getValue(), false, inst));
        }
        monos.add(new InferenceResult<>(sort, varSorts));
      } catch (SortInferenceError e) {
        lastError = e;
      }
    }
    if (monos.isEmpty()) {
      throw lastError;
    }
    return monos;
  }

  /**
   * Convert a CompactSort into a K-Sort
   *
   * @param sort - A compact sort
   * @param polarity - The polarity in which sort occurs. True for positive, false for negative.
   * @param instantiation - A map indicating how the variables in sort should be instantiated
   * @return An equivalent Sort
   */
  private Sort compactSortToSort(
      CompactSort sort, boolean polarity, Map<BoundedSort.Variable, Sort> instantiation)
      throws SortInferenceError {
    Set<Sort> sorts = sort.vars().stream().map(instantiation::get).collect(Collectors.toSet());
    sorts.addAll(
        sort.ctors().stream()
            .map(h -> new org.kframework.kore.ADT.Sort(h.name(), Seq()))
            .collect(Collectors.toSet()));
    Set<Sort> bounds =
        polarity ? mod.subsorts().upperBounds(sorts) : mod.subsorts().lowerBounds(sorts);
    Set<Sort> candidates =
        polarity ? mod.subsorts().minimal(bounds) : mod.subsorts().maximal(bounds);
    if (candidates.size() != 1) {
      throw SortInferenceError.boundsError(sorts, candidates, polarity);
    }
    return candidates.iterator().next();
  }

  private Set<Map<BoundedSort.Variable, Sort>> monomorphizeInVar(
      Map<BoundedSort.Variable, Sort> instantiation,
      BoundedSort.Variable var,
      Map<Tuple2<BoundedSort.Variable, Boolean>, Set<BoundedSort>> bounds) {

    Map<Boolean, Set<Sort>> polBounds = new HashMap<>();
    polBounds.put(true, new HashSet<>());
    polBounds.put(false, new HashSet<>());

    for (Entry<Boolean, Set<Sort>> polBound : polBounds.entrySet()) {
      for (BoundedSort bSort :
          bounds.getOrDefault(Tuple2.apply(var, polBound.getKey()), new HashSet<>())) {
        if (bSort instanceof BoundedSort.Variable bVar) {
          if (instantiation.containsKey(bVar)) {
            polBound.getValue().add(instantiation.get(bVar));
          }
        } else if (bSort instanceof BoundedSort.Constructor lowerCtor) {
          polBound.getValue().add(new org.kframework.kore.ADT.Sort(lowerCtor.head().name(), Seq()));
        }
      }
    }

    Set<Sort> range = mod.subsorts().upperBounds(polBounds.get(true));
    range.retainAll(mod.subsorts().lowerBounds(polBounds.get(false)));

    Set<Map<BoundedSort.Variable, Sort>> insts = new HashSet<>();
    for (Sort sort : range) {
      Map<BoundedSort.Variable, Sort> inst = new HashMap<>(instantiation);
      inst.put(var, sort);
      insts.add(inst);
    }
    return insts;
  }

  // The type of cast which wraps the current term being typed
  private enum CastContext {
    NONE,
    SEMANTIC_CAST,
    STRICT_CAST
  }

  private Term insertCasts(Term t, InferenceResult<Sort> sorts, CastContext castCtx) {
    if (t instanceof Ambiguity) {
      throw new AssertionError("Ambiguities are not yet supported!");
    }

    ProductionReference pr = (ProductionReference) t;
    if (pr instanceof Constant c) {
      if (c.production().sort().equals(Sorts.KVariable())
          || c.production().sort().equals(Sorts.KConfigVar())) {
        Sort inferred = sorts.varSorts().get(varName(c));
        return wrapTermWithCast(c, inferred, castCtx);
      }
      return c;
    }

    TermCons tc = (TermCons) pr;
    CastContext newCtx = CastContext.NONE;
    if (tc.production().klabel().isDefined()) {
      KLabel klabel = tc.production().klabel().get();
      String label = klabel.name();
      if (label.startsWith("#SemanticCastTo")) {
        newCtx = CastContext.SEMANTIC_CAST;
      } else if (label.equals("#SyntacticCast") || label.equals("#InnerCast")) {
        newCtx = CastContext.STRICT_CAST;
      }
    }
    for (int i = 0; i < tc.items().size(); i++) {
      tc = tc.with(i, insertCasts(tc.get(i), sorts, newCtx));
    }
    return tc;
  }

  private Term wrapTermWithCast(Term t, Sort sort, CastContext castCtx) {
    Production cast = null;
    switch (castMode) {
      case NONE -> {}
      case SEMANTIC_CASTS_ON_ALL_VARS -> {
        if (castCtx != CastContext.SEMANTIC_CAST) {
          cast = mod.productionsFor().apply(KLabel("#SemanticCastTo" + sort.toString())).head();
        }
      }
      case STRICT_CASTS_ON_UNCASTED_VARS -> {
        if (castCtx == CastContext.NONE) {
          cast =
              stream(mod.productionsFor().apply(KLabel("#SyntacticCast")))
                  .filter(p -> p.sort().equals(sort))
                  .findAny()
                  .orElseThrow(
                      () ->
                          new AssertionError(
                              "Attempting to insert strict cast to "
                                  + sort
                                  + ", but no appropriate #SyntacticCast production found."));
        }
      }
    }

    if (cast == null) {
      return t;
    }
    return TermCons.apply(ConsPStack.singleton(t), cast, t.location(), t.source());
  }

  private String locStr(ProductionReference pr) {
    String suffix = "";
    if (pr.production().klabel().isDefined()) {
      suffix = "_" + pr.production().klabel().get().name().replace("|", "");
    }
    if (pr.location().isPresent()) {
      Location l = pr.location().get();
      return l.startLine()
          + "_"
          + l.startColumn()
          + "_"
          + l.endLine()
          + "_"
          + l.endColumn()
          + suffix;
    }
    assert prIds.containsKey(pr);
    return prIds.get(pr) + suffix;
  }

  public String varName(Constant var) {
    if (ResolveAnonVar.isAnonVarOrNamedAnonVar(KVariable(var.value()))) {
      return "Var_" + var.value() + "_" + locStr(var);
    }
    return "Var" + var.value();
  }

  public String paramName(ProductionReference pr, Sort param) {
    return "Param_" + param.name() + "_" + locStr(pr);
  }

  private static Term stripBrackets(Term tc) {
    Term child = tc;
    while (child instanceof TermCons
        && ((TermCons) child).production().att().contains(Att.BRACKET())) {
      child = ((TermCons) child).get(0);
    }
    return child;
  }

  private static BoundedSort sortToBoundedSort(
      Sort sort,
      ProductionReference pr,
      Map<Tuple2<ProductionReference, Sort>, BoundedSort.Variable> params) {
    if (pr.production().params().contains(sort)) {
      return params.get(Tuple2.apply(pr, sort));
    }
    return new BoundedSort.Constructor(sort.head());
  }

  /**
   * @param sort - The sort to convert, which must not contain any sort variables!
   * @return sort as a BoundedSort
   */
  private static BoundedSort.Constructor sortWithoutSortVariablesToBoundedSort(Sort sort) {
    return new BoundedSort.Constructor(sort.head());
  }
}

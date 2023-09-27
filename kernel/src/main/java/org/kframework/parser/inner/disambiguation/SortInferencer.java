package org.kframework.parser.inner.disambiguation;

import com.google.gson.GsonBuilder;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
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
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.utils.errorsystem.KEMException;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

/*
 * Disambiguation transformer which performs type checking and infers the sorts of variables.
 *
 * The overall design is based on the algorithm described in
 * "The Simple Essence of Algebraic Subtyping: Principal Type Inference with Subtyping Made Easy" by Lionel Parreaux.
 *
 * Specifically, we can straightforwardly treat any (non-ambiguous) term in our language as a function in the SimpleSub
 *
 * - Constants are treated as built-ins
 * - TermCons are treated as primitive functions
 */
public class SortInferencer {
    private final Module mod;

    private int id = 0;

    private final PrintWriter debug;

    private final boolean inferSortChecks;

    private final boolean inferCasts;

    //
    public SortInferencer(Module mod, PrintWriter debug, boolean inferSortChecks, boolean inferCasts) {
        this.mod = mod;
        this.debug = debug;
        this.inferSortChecks = inferSortChecks;
        this.inferCasts = inferCasts;
    }

    public Either<Set<KEMException>, Term> apply(Term t, Sort topSort, boolean isAnywhereRule) {
        // Avoid some special casing by inserting t into an Ambiguity node
        Ambiguity topAmb;
        if (t instanceof Ambiguity) {
            topAmb = (Ambiguity) t;
        } else {
            Set<Term> items = new HashSet<>();
            items.add(t);
            topAmb = new Ambiguity(items);
        }

        // Infer an unsimplified type for each unambiguous slice of the parse forest parametric over its
        // contained ambiguities
        Map<Ambiguity, Map<Term, Optional<InferenceResult<BoundedSort>>>> unsimplifiedSlices = new HashMap<>();
        try {
            inferAllSlices(topAmb, isAnywhereRule, Optional.of(topSort), unsimplifiedSlices);
        } catch (SortInferenceError e) {
            Set<KEMException> errs = new HashSet<>();
            errs.add(KEMException.innerParserError(e.getMessage(), e.getProductionReference()));
            return Left.apply(errs);
        }

        debug.println(new GsonBuilder().setPrettyPrinting().create().toJson(unsimplifiedSlices));

        // Convert to compact types and simplify
        Map<Ambiguity, Map<Term, Optional<InferenceResult<CompactSort>>>> slices = new HashMap<>();
        for (Ambiguity amb : unsimplifiedSlices.keySet()) {
            Map<Term, Optional<InferenceResult<CompactSort>>> sliceRes = new HashMap<>();
            for (Map.Entry<Term, Optional<InferenceResult<BoundedSort>>> entry :
                    unsimplifiedSlices.get(amb).entrySet()) {
                Optional<InferenceResult<CompactSort>> simplified = entry.getValue().map(this::compact);
                simplified.ifPresent(this::simplify);
                sliceRes.put(entry.getKey(), simplified);
            }
        }

        // Propagate ambiguities upwards to collect all well-typed parses

        // Monomorphize each result to assign concrete types
        return null;
    }

    /**
     *
     * @param t - The term to collect ambiguities of
     * @param result - The set of all ambiguities which are contained in t,
     *                 but are not themselves contained within any other ambiguity.
     */
    private void collectChildAmbiguities(Term t, Set<Ambiguity> result) {
        if (t instanceof Ambiguity) {
            result.add((Ambiguity) t);
            return;
        }

        if (t instanceof TermCons) {
            for (Term item : ((TermCons) t).items()) {
                collectChildAmbiguities(item, result);
            }
        }
    }

    /**
     * @param amb - The Ambiguity to infer all slices of.
     * @param topSort - The expected sort of the top of the term.
     * @param isAnywhereRule - Whether t is an anywhere rule
     * @param result - An output parameter used to store the result of inferring all slices.
     *                 This is passed as an argument so that it can also be used as a cache throughout.
     *  The final result is a map with entries A |-> M as follows:
     *  - A is an ambiguity node in t
     *  - M is a map from A's items to their InferenceResults (or Optional.empty() if the item is ill-typed)
     *  Note that if an item is ill-typed, we do not explore its contained ambiguities, so they may not be
     *  present as keys in the final map.
     *
     * @throws SortInferenceError if none of the possible parses of t are well-typed
     */        
    private void inferAllSlices(Ambiguity amb, boolean isAnywhereRule, Optional<Sort> topSort,
                                Map<Ambiguity, Map<Term, Optional<InferenceResult<BoundedSort>>>> result)
            throws SortInferenceError {
        if (result.containsKey(amb)) {
            return;
        }
        boolean hasWellTypedItem = false;
        SortInferenceError lastError = null;
        Map<Term, Optional<InferenceResult<BoundedSort>>> itemResults = new HashMap<>();
        for (Term item : amb.items()) {
            try {
                InferenceState itemState =
                        new InferenceState(new HashMap<>(), new HashMap<>(), new HashMap<>(), new HashSet<>());
                BoundedSort itemSort = infer(item, isAnywhereRule, itemState);

                if (topSort.isPresent()) {
                    BoundedSort topBoundedSort = sortWithoutSortVariablesToBoundedSort(topSort.get());
                    constrain(itemSort, topBoundedSort, itemState, (ProductionReference) item);
                    itemSort = topBoundedSort;
                }

                Set<Ambiguity> childAmbiguities = new HashSet<>();
                collectChildAmbiguities(item, childAmbiguities);
                for (Ambiguity childAmb : childAmbiguities) {
                    inferAllSlices(childAmb, isAnywhereRule, Optional.empty(), result);
                }

                itemResults.put(item, Optional.of(new InferenceResult<>(itemSort, itemState.varSorts(), itemState.ambSorts())));

                hasWellTypedItem = true;
            } catch (SortInferenceError e) {
                itemResults.put(item, Optional.empty());
                lastError = e;
            }
        }
        if (!hasWellTypedItem && lastError != null) {
            // None of the ambiguity branches type check, so arbitrarily pick the last error to propagate upward
            throw lastError;
        }
        result.put(amb, itemResults);
    }

    private static class SortInferenceError extends Exception {
        private final ProductionReference pr;

        private static String message(Sort lhs, Sort rhs, ProductionReference pr) {
            String msg;
            if (pr instanceof Constant) {
                msg = "Unexpected sort " + lhs + " for term " + ((Constant)pr).value() + ". Expected " + rhs + ".";
            } else {
                msg = "Unexpected sort " + lhs + " for term parsed as production " + pr.production() +
                        ". Expected " + rhs + ".";
            }
            return msg;
        }

        public SortInferenceError(Sort lhs, Sort rhs, ProductionReference pr) {
            super(message(lhs, rhs, pr));
            this.pr = pr;
        }

        ProductionReference getProductionReference() {
            return pr;
        }
    }


    /**
     *
     * @param t - The term we want to infer the type of
     * @param isAnywhereRule - Whether t is an anywhere rule
     * @param inferState - All state maintained during inference, which will be updated throughout
     *                     with sorts for all contained variables and ambiguities
     *
     * @return The unsimplified sort of the input term parametric over any contained ambiguities.
     * @throws SortInferenceError - an exception indicating that the term is not well-typed
     */
    private BoundedSort infer(Term t, boolean isAnywhereRule,
                              InferenceState inferState) throws SortInferenceError {
        if (t instanceof Ambiguity) {
            BoundedSort.Variable ambVar = new BoundedSort.Variable(new ArrayList<>(), new ArrayList<>(), Optional.empty());
            inferState.ambSorts().put((Ambiguity) t, ambVar);
            return ambVar;
        }

        ProductionReference pr = (ProductionReference) t;
        if (pr.id().isEmpty()) {
            pr.setId(Optional.of(id));
            id++;
        }
        addParamsFromProduction(inferState, pr);

        if (pr instanceof Constant) {
            Constant c = (Constant) t;
            if (c.production().sort().equals(Sorts.KVariable()) || c.production().sort().equals(Sorts.KConfigVar())) {
                String name = varName(c);
                if (!inferState.varSorts().containsKey(name)) {
                    inferState.varSorts().put(name,
                            new BoundedSort.Variable(new ArrayList<>(), new ArrayList<>(), Optional.of(name)));
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
                BoundedSort childSort = infer(tc.get(0), false, inferState);
                BoundedSort castedSort = sortToBoundedSort(
                        label.equals("#InnerCast") ? ((NonTerminal) tc.production().items().apply(1)).sort() : tc.production().sort(),
                        pr, inferState.params());
                debug.println("Ignoring strict cast!");
                constrain(childSort, castedSort, inferState, pr);
                // TODO: Unify here instead of constraining!
                return childSort;
            }

            // For function, macro, and anywhere rules, the RHS must be a subsort of the LHS
            if (klabel.head().equals(KLabels.KREWRITE)) {
                if (isAnywhereRule || isFunctionOrMacro(tc.get(0))) {
                    BoundedSort lhsSort = infer (tc.get(0), isAnywhereRule, inferState);
                    BoundedSort rhsSort = infer(tc.get(1), isAnywhereRule, inferState);
                    constrain(rhsSort, lhsSort, inferState, pr);
                    return lhsSort;
                }
            }
        }

        for (int prodI = 0, tcI = 0; prodI < tc.production().items().size(); prodI++) {
            if (!(tc.production().items().apply(prodI) instanceof NonTerminal)) {
                continue;
            }
            NonTerminal nt = (NonTerminal) tc.production().items().apply(prodI);
            BoundedSort expectedSort = sortToBoundedSort(nt.sort(), pr, inferState.params());
            BoundedSort childSort = infer(tc.get(tcI), isAnywhereRule, inferState);
            constrain(childSort, expectedSort, inferState, pr);
            tcI++;
        }
        BoundedSort resSort = new BoundedSort.Variable(new ArrayList<>(), new ArrayList<>(), Optional.empty());
        constrain(sortToBoundedSort(tc.production().sort(), pr, inferState.params()), resSort, inferState, pr);
        return resSort;
    }

    private static boolean isFunctionOrMacro(Term tc) {
        Term raw = stripBrackets(tc);
        if (raw instanceof ProductionReference) {
            ProductionReference pr = (ProductionReference) raw;
            return pr.production().att().contains(Att.FUNCTION()) || ExpandMacros.isMacro(pr.production());
        }
        return false;
    }

    private static void addParamsFromProduction(InferenceState inferState, ProductionReference pr) {
        for (Sort param : iterable(pr.production().params())) {
            inferState.params().put(Tuple2.apply(pr, param),
                    new BoundedSort.Variable(new ArrayList<>(), new ArrayList<>(), Optional.of(paramName(pr, param))));
        }
    }

    private void constrain(BoundedSort lhs, BoundedSort rhs, InferenceState inferState, ProductionReference pr)
            throws SortInferenceError {
        if (lhs.equals(rhs) ||
                inferState.constraintCache().contains(Tuple2.apply(lhs, rhs))) {
            return;
        }

        if (lhs instanceof BoundedSort.Variable) {
            BoundedSort.Variable lhsVar = (BoundedSort.Variable) lhs;
            inferState.constraintCache().add(Tuple2.apply(lhs, rhs));
            lhsVar.upperBounds().add(rhs);
            for (BoundedSort lhsLower : lhsVar.lowerBounds()) {
                constrain(lhsLower, rhs, inferState, pr);
            }
            return;
        }

        if (rhs instanceof BoundedSort.Variable) {
            BoundedSort.Variable rhsVar = (BoundedSort.Variable) rhs;
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
            throw new SortInferenceError(lhsSort, rhsSort, pr);
        }

        throw new AssertionError("Parametric sorts are not yet implemented!");
    }

    private CompactSort compact(BoundedSort sort, boolean polarity) {
        if (sort instanceof BoundedSort.Constructor) {
            BoundedSort.Constructor ctor = (BoundedSort.Constructor) sort;
            if (ctor.head().params() == 0) {
                Set<Tuple2<SortHead, List<CompactSort>>> ctors = new HashSet<>();
                ctors.add(Tuple2.apply(ctor.head(), new ArrayList<>()));
                return new CompactSort(new HashSet<>(), ctors);
            }
            throw new AssertionError("Parametric sorts are not yet implemented!");
        }
        BoundedSort.Variable var = (BoundedSort.Variable) sort;
        List<BoundedSort> bounds = polarity ? var.lowerBounds() : var.upperBounds();

        Set<BoundedSort.Variable> vars = new HashSet<>();
        Set<Tuple2<SortHead, List<CompactSort>>> ctors = new HashSet<>();
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
        
        Map<Ambiguity, CompactSort> ambSorts = new HashMap<>();
        for (Map.Entry<Ambiguity, BoundedSort> entry : res.ambSorts().entrySet()) {
            ambSorts.put(entry.getKey(), compact(entry.getValue(), false));
        }

        return new InferenceResult<>(sort, varSorts, ambSorts);
    }

    private void simplify(InferenceResult<CompactSort> res) {

        // We model terms as functions from their variable sorts to the term's sort.
        // For a slice, the contained ambiguities are also inputs to this function.
        // As a result, any variable or ambiguity's sort occurs in negative position.

        Set<BoundedSort.Variable> allVars = new HashSet<>();
        Map<Tuple2<BoundedSort.Variable, Boolean>, Set<BoundedSort>> coOccurrences = new HashMap<>();


        Map<BoundedSort.Variable, Optional<BoundedSort.Variable>> varSubst = new HashMap<>();


        // If two type variables occur in exactly the same set of negative (resp. positive) positions,
        // they are indistinguishable and can be unified


        // Flatten variable sandwiches t <: a <: t



    }

    private static String locStr(ProductionReference pr) {
        String suffix = "";
        if (pr.production().klabel().isDefined()) {
            suffix = "_" + pr.production().klabel().get().name().replace("|","");
        }
        if (pr.location().isPresent()) {
            Location l = pr.location().get();
            return l.startLine() + "_" + l.startColumn() + "_" + l.endLine() + "_" + l.endColumn() + suffix;
        }
        assert pr.id().isPresent();
        return pr.id().get() + suffix;
    }

    public static String varName(Constant var) {
        if (ResolveAnonVar.isAnonVarOrNamedAnonVar(KVariable(var.value()))) {
            return "Var_" + var.value() + "_" + locStr(var);
        }
        return "Var" + var.value();
    }

    public static String paramName(ProductionReference pr, Sort param) {
        return "Param_" + param.name() + "_" + locStr(pr);
    }

    private static Term stripBrackets(Term tc) {
        Term child = tc;
        while (child instanceof TermCons &&
                ((TermCons) child).production().att().contains(Att.BRACKET())) {
            child = ((TermCons) child).get(0);
        }
        return child;
    }

    private static BoundedSort
    sortToBoundedSort(Sort sort, ProductionReference pr, Map<Tuple2<ProductionReference, Sort>, BoundedSort.Variable> params) {
        if (pr.production().params().contains(sort)) {
            return params.get(Tuple2.apply(pr, sort));
        }
        return new BoundedSort.Constructor(
                sort.head(),
                stream(sort.params()).map((p) -> sortToBoundedSort(p, pr, params)).collect(Collectors.toList()));
    }

    /**
     * @param sort - The sort to convert, which must not contain any sort variables!
     * @return sort as a BoundedSort
     */
    private static BoundedSort.Constructor sortWithoutSortVariablesToBoundedSort(Sort sort) {
        return new BoundedSort.Constructor(
                sort.head(),
                stream(sort.params()).map(SortInferencer::sortWithoutSortVariablesToBoundedSort)
                        .collect(Collectors.toList()));
    }
}

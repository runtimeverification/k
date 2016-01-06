// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.attributes.Location;
import org.kframework.builtin.Sorts;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import org.kframework.kore.compile.ResolveAnonVar;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.SetsGeneralTransformer;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.VariableTypeClashException;
import org.pcollections.ConsPStack;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * Apply the priority and associativity filters.
 */
public class VariableTypeInferenceFilter extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {
    public enum VarType { CONTEXT, USER }
    private final POSet<Sort> subsorts;
    private final scala.collection.Set<Sort> sortSet;
    private final scala.collection.Map<KLabel, scala.collection.Set<Production>> productions;
    private final boolean inferSortChecks;
    private Set<ParseFailedException> warnings = Sets.newHashSet();
    public VariableTypeInferenceFilter(POSet<Sort> subsorts, scala.collection.Set<Sort> sortSet, scala.collection.Map<
            KLabel, scala.collection.Set<Production>> productions, boolean inferSortChecks) {
        this.subsorts = subsorts;
        this.sortSet = sortSet;
        this.productions = productions;
        this.inferSortChecks = inferSortChecks;
    }

    /** Return the set of all known sorts which are a lower bound on
     * all sorts in {@code bounds}, leaving out internal sorts below "KBott" or above "K".
     */
    private Set<Sort> lowerBounds(Collection<Sort> bounds) {
        Set<Sort> mins = new HashSet<>();
        nextsort:
        for (Sort sort : iterable(sortSet)) { // for every declared sort
            // Sorts at or below KBott, or above K, are assumed to be
            // sorts from kast.k representing meta-syntax that is not a real sort.
            // This is done to prevent variables from being inferred as KBott or
            // as KList.
            if (subsorts.lessThanEq(sort, Sort("KBott")))
                continue;
            if (subsorts.greaterThan(sort, Sort("K")))
                continue;
            for (Sort bound : bounds)
                if (!subsorts.greaterThanEq(bound, sort))
                    continue nextsort;
            mins.add(sort);
        }
        return mins;
    }

    // When passed a mutable List {@code sets} of nonempty subsets of {@code universe},
    // returns a set containing at least one item in common with each of the sets.
    // Empties {@code sets}.
    private <T> Set<T> hittingSet(Set<T> universe, List<Set<T>> sets) {
        assert sets.stream().allMatch(s -> !s.isEmpty());
        Set<T> hittingSet = new HashSet<>();
        while (!sets.isEmpty()) {
            T maxItem = null;
            int maxCount = 0;
            for (T item : universe) {
                int count = 0;
                for (Set<T> s : sets) {
                    if (s.contains(item)) {
                        ++count;
                    }
                }
                if (count > maxCount) {
                    maxItem = item;
                    maxCount = count;
                }
            }
            hittingSet.add(maxItem);
            ListIterator<Set<T>> li = sets.listIterator();
            while (li.hasNext()) {
                if (li.next().contains(maxItem)) {
                    li.remove();
                }
            }
        }
        return hittingSet;
    }

    static final class VarKey {
        private final Constant var;
        private VarKey(Constant c) {
            var = c;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof VarKey)) return false;

            VarKey vo = (VarKey)o;
            return var.equals(vo.var) && var.source().equals(vo.var.source()) && var.location().equals(vo.var.location());
        }

        @Override
        public int hashCode() {
            return var.hashCode();
        }

        @Override
        public String toString() {
            if (var.location().isPresent()) {
                return '\''+var.value()+"' at "+var.location().get();
            } else {
                return '\''+var.value()+'\'';
            }
        }

        public boolean isAnyVar() {
            return var.value().equals(ResolveAnonVar.ANON_VAR.name());
        }
    }

    private static VarKey getVarKey(Constant c) {
        if (c.value().equals(ResolveAnonVar.ANON_VAR.name())) {
            return new VarKey(c); // wildcard values are compared including location
        } else {
            return new VarKey(Constant.apply(c.value(), c.production(), Optional.empty(), Optional.empty()));
        }
    }

    @Override
    public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<ParseFailedException>> apply(Term t) {
        Term loc = t;
        if (loc instanceof Ambiguity) {
            loc = ((Ambiguity)loc).items().iterator().next();
        }

        Set<VarInfo> vis = new CollectVariables().apply(t)._2();
        //System.out.println("vis = " + vis);
        Map<VarKey, Sort> decl = new HashMap<>();
        for (VarInfo vi : vis) {
            Sort s = decl.get(vi.varKey);
            if (vi.varType == VarType.USER) {
                if (s == null) {
                    decl.put(vi.varKey, vi.sort);
                } else if (!s.equals(vi.sort)) {
                    String msg = vi.varKey + " declared with two different sorts: " + s + " and " + vi.sort;
                    //System.out.println(msg);
                    KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, loc.source().get(), loc.location().get());
                    return simpleError(Sets.newHashSet(new VariableTypeClashException(kex)));
                }
            }
        }

        //System.out.println("decl = " + decl);
        Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck(decl).apply(t);
        if (rez.isLeft())
            return Tuple2.apply(rez, Sets.newHashSet());
        else
            t = rez.right().get();

        boolean varTypeInference = true;
        if (varTypeInference) {
            CollectExpectedVariablesVisitor vars2 = new CollectExpectedVariablesVisitor(decl.keySet());
            vars2.apply(t);
            //System.out.println("vars = " + vars2.vars);

            Set<Multimap<VarKey, Sort>> solutions = new HashSet<>();
            VarKey fails = null;
            for (Multimap<VarKey, Sort> variant : vars2.vars) {
                // take each solution and do GLB on every variable
                Multimap<VarKey, Sort> solution = HashMultimap.create();
                for (VarKey key : variant.keySet()) {
                    Collection<Sort> values = variant.get(key);
                    Set<Sort> mins = lowerBounds(values);
                    if (mins.size() == 0) {
                        fails = key;
                        solution.clear();
                        break;
                    } else {
                        solution.putAll(key, subsorts.maximal(mins));
                    }
                }
                // I found a solution that fits everywhere, then store it for disambiguation
                if (!solution.isEmpty())
                    solutions.add(solution);
            }
            if (!vars2.vars.isEmpty()) {
                if (solutions.size() == 0) {
                    assert fails != null;
                    String msg = "Could not infer a sort for variable " + fails + " to match every location.";
                    KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, loc.source().get(), loc.location().get());
                    return simpleError(Sets.newHashSet(new VariableTypeClashException(kex)));
                }

                // If multiple parses were typeable, check that all have the same set of variables
                if (solutions.size() > 1) {
                    Set<VarKey> allVars = new HashSet<>();
                    Set<VarKey> commonVars = null;
                    for (Multimap<VarKey, Sort> solution : solutions) {
                        Set<VarKey> theseVars = solution.keySet();
                        allVars.addAll(theseVars);
                        if (commonVars == null) {
                            commonVars = new HashSet<>(theseVars);
                        } else {
                            commonVars.retainAll(theseVars);
                        }
                    }
                    if (!allVars.equals(commonVars)) {
                        String msg = "Possible parses have different sets of variables. "
                                + "Each of these may or may not be a variable, depending on the parse:";
                        allVars.removeAll(commonVars);
                        for (VarKey v : allVars) {
                            msg += " " + v;
                        }
                        KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, loc.source().get(), loc.location().get());
                        return simpleError(Sets.newHashSet(new ParseFailedException(kex)));
                    }
                }

                // Now check that each variable has a unique maximal possible sort.
                Multimap<VarKey,Sort> varBounds;
                if (solutions.size() > 1) {
                    varBounds = HashMultimap.create();
                    for (Multimap<VarKey, Sort> solution : solutions) {
                        varBounds.putAll(solution);
                    }
                } else {
                    varBounds = solutions.iterator().next();
                }
                Multimap<VarKey,Sort> solution = HashMultimap.create();
                for (VarKey k : varBounds.keySet()) {
                    Set<Sort> sorts = subsorts.maximal(varBounds.get(k));
                    if (sorts.size() > 1) {
                        String msg = "Could not infer a unique sort for variable " + k + ".";
                        msg += " Possible sorts: ";
                        for (Sort vv1 : sorts)
                            msg += vv1 + ", ";
                        msg = msg.substring(0, msg.length() - 2);
                        KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, loc.source().get(), loc.location().get());
                        return simpleError(Sets.newHashSet(new VariableTypeClashException(kex)));
                    }
                    solution.putAll(k, sorts);
                }

                if (!solutions.contains(solution)) {
                    List<Set<VarKey>> badVars = new ArrayList<>(solutions.size());
                    for (Multimap<VarKey,Sort> badSolution : solutions) {
                        HashSet<VarKey> myBadVars = new HashSet<>();
                        for (VarKey k : badSolution.keySet()) {
                            if (!badSolution.get(k).equals(solution.get(k))) {
                                myBadVars.add(k);
                            }
                        }
                        badVars.add(myBadVars);
                    }
                    Set<VarKey> reportVars = hittingSet(solution.keySet(), badVars);
                    String msg = "Could not infer unique sorts. Each variable has a unique greatest possible sort,"
                            +" but these cannot all be assigned simultaneously: ";
                    for (VarKey v : solution.keySet()) {
                        msg+= v+" : "+solution.get(v).iterator().next()+", ";
                    }
                    msg = msg.substring(0, msg.length() - 2);
                    KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, loc.source().get(), loc.location().get());
                    return simpleError(Sets.newHashSet(new VariableTypeClashException(kex)));
                } else {
                    //System.out.println("solutions = " + solutions);
                    decl.clear();
                    for (VarKey key : solution.keySet()) {
                        Sort sort = solution.get(key).iterator().next();
                        decl.put(key, sort);
                        if (!key.isAnyVar()) {
                            String msg = "Variable " + key + " was not declared. Assuming sort " + sort + ".";
                            warnings.add(new VariableTypeClashException(
                                    new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.COMPILER, msg, loc.source().get(), loc.location().get())));
                        }
                    }
                    // after type inference for concrete sorts, reject erroneous branches
                    if (!decl.isEmpty()) {
                        t = new ApplyTypeCheck(decl).apply(t).right().get();
                    }
                }
            }
        }

        // type inference and error reporting
        // -- Error: type mismatch for variable... (when the declared variable doesn't fit everywhere)
        // -- Error: could not infer a sort for variable... (when there is no solution left)
        // -- Error: could not infer a unique sort for variable... (when there is more than one solution)
        // -- Warning: untyped variable, assuming sort...

        return new Tuple2<>(Right.apply(t), warnings);
    }

    private class VarInfo {
        public VarKey varKey;
        public Sort sort;
        public Location loc;
        public VarType varType;

        public VarInfo(Constant varOcc, Sort sort, VarType varType) {
            this.varKey = getVarKey(varOcc);
            this.sort = sort;
            this.loc = varOcc.location().get();
            this.varType = varType;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof VarInfo)) return false;

            VarInfo varInfo = (VarInfo) o;

            if (!loc.equals(varInfo.loc)) return false;
            if (!sort.equals(varInfo.sort)) return false;
            if (!varKey.equals(varInfo.varKey)) return false;
            if (varType != varInfo.varType) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = varKey.hashCode();
            result = 31 * result + sort.hashCode();
            result = 31 * result + loc.hashCode();
            result = 31 * result + varType.hashCode();
            return result;
        }

        @Override
        public String toString() {
            return "VarInfo{" +
                    "" + varKey +
                    ", " + sort +
                    ", " + loc +
                    ", " + varType +
                    '}';
        }
    }

    public static Sort getSortOfCast(TermCons tc) {
        switch (tc.production().klabel().get().name()) {
        case "#SyntacticCast":
        case "#OuterCast":
            return tc.production().sort();
        case "#InnerCast":
            return ((NonTerminal)tc.production().items().apply(0)).sort();
        default:
            if (tc.production().klabel().get().name().startsWith("#SemanticCastTo")) {
                return tc.production().sort();
            }
            throw new AssertionError("Unexpected cast type");
        }
    }

    private class CollectVariables extends SetsGeneralTransformer<ParseFailedException, VarInfo> {
        public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> apply(TermCons tc) {
            // TODO: (Radu) if this is cast, take the sort from annotations?
            Set<VarInfo> collector = Sets.newHashSet();
            if (tc.production().klabel().isDefined()
                    && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                    || tc.production().klabel().get().name().equals("#InnerCast"))) {
                Term t = tc.get(0);
                collector = new CollectVariables2(getSortOfCast(tc), VarType.USER).apply(t)._2();
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.get(j);
                        Set<VarInfo> vars = new CollectVariables2(((NonTerminal) tc.production().items().apply(i)).sort(), VarType.CONTEXT).apply(t)._2();
                        collector.addAll(vars);
                        j++;
                    }
                }
            }
            Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> rez = super.apply(tc);
            return new Tuple2<>(Right.apply(rez._1().right().get()), mergeWarnings(collector, rez._2()));
        }

        private class CollectVariables2 extends SetsGeneralTransformer<ParseFailedException, VarInfo> {
            private final Sort sort;
            private final VarType varType;
            public CollectVariables2(Sort sort, VarType varType) {
                this.sort = sort;
                this.varType = varType;
            }

            public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> apply(TermCons tc) {
                if (tc.production().att().contains("bracket")
                        || (tc.production().klabel().isDefined()
                            && tc.production().klabel().get().equals(KLabel("#KRewrite")))) {
                   return super.apply(tc);
                }
                return simpleResult(tc);
            }

            public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> apply(Constant c) {
                if (c.production().sort().equals(Sorts.KVariable())) {
                    return new Tuple2<>(Right.apply(c), Sets.newHashSet(new VarInfo(c, this.sort, varType)));
                }
                return simpleResult(c);
            }
        }
    }

    private class ApplyTypeCheck extends SetsTransformerWithErrors<ParseFailedException> {
        private final Map<VarKey, Sort> decl;
        public ApplyTypeCheck(Map<VarKey, Sort> decl) {
            this.decl = decl;
        }

        public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
            if (tc.production().klabel().isDefined()
                    && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                    || tc.production().klabel().get().name().equals("#InnerCast"))) {
                Term t = tc.get(0);
                boolean strictSortEquality = !tc.production().klabel().get().name().startsWith("#SemanticCastTo");
                Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck2(getSortOfCast(tc), true, strictSortEquality, strictSortEquality && inferSortChecks).apply(t);
                if (rez.isLeft())
                    return rez;
                tc = tc.with(0, rez.right().get());
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.get(j);
                        Sort s = ((NonTerminal) tc.production().items().apply(i)).sort();
                        Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck2(s, false, false, inferSortChecks).apply(t);
                        if (rez.isLeft())
                            return rez;
                        tc = tc.with(j, rez.right().get());
                        j++;
                    }
                }
            }
            Either<java.util.Set<ParseFailedException>, Term> rez = super.apply(tc);
            if (rez.isLeft())
                return rez;
            return Right.apply(rez.right().get());
        }

        private class ApplyTypeCheck2 extends SetsTransformerWithErrors<ParseFailedException> {
            private final Sort sort;
            private final boolean hasCastAlready;
            private final boolean strictSortEquality;
            private final boolean addCast;

            public ApplyTypeCheck2(Sort sort, boolean hasCastAlready, boolean strictSortEquality, boolean addCast) {
                this.sort = sort;
                this.hasCastAlready = hasCastAlready;
                this.strictSortEquality = strictSortEquality;
                this.addCast = addCast;
            }

            public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
                if (tc.production().att().contains("bracket")
                        || (tc.production().klabel().isDefined()
                        && tc.production().klabel().get().equals(KLabel("#KRewrite")))) {
                    return super.apply(tc);
                }
                return Right.apply(tc);
            }

            public Either<java.util.Set<ParseFailedException>, Term> apply(Constant c) {
                if (c.production().sort().equals(Sorts.KVariable())) {
                    Sort declared = decl.get(getVarKey(c));
                    if (declared != null && !declared.equals(Sorts.K())) {
                        if ((!strictSortEquality && !subsorts.lessThanEq(declared, sort)) || (strictSortEquality && !declared.equals(sort))) {
                            String msg = "Unexpected sort " + declared + " for term " + c.value() + ". Expected " + sort + ".";
                            KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, c.source().get(), c.location().get());
                            return Left.apply(Sets.newHashSet(new VariableTypeClashException(kex)));
                        }
                        return wrapTermWithCast(c, declared);
                    }
                }
                return Right.apply(c);
            }

            private Either<Set<ParseFailedException>, Term> wrapTermWithCast(Constant c, Sort declared) {
                Production cast;
                if (addCast) {
                    cast = productions.apply(KLabel("#SemanticCastTo" + declared.name())).head();
                } else if (!hasCastAlready) {
                    cast = stream(productions.apply(KLabel("#SyntacticCast"))).filter(p -> p.sort().equals(declared)).findAny().get();
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

    public class CollectExpectedVariablesVisitor extends SafeTransformer {
        /**
         * Each element in the list is a Mapping from variable name and a list of constraints for that variable.
         * On each Ambiguity node, a cartesian product is created between the current List and each ambiguity variant.
         */
        public Set<Multimap<VarKey, Sort>> vars = new HashSet<>();
        private final Set<VarKey> declaredNames;

        public CollectExpectedVariablesVisitor(Set<VarKey> declaredNames) {
            this.declaredNames = declaredNames;
        }

        @Override
        public Term apply(Ambiguity node) {
            Set<Multimap<VarKey, Sort>> newVars = new HashSet<>();
            for (Term t : node.items()) {
                CollectExpectedVariablesVisitor viz = new CollectExpectedVariablesVisitor(declaredNames);
                viz.apply(t);
                // create the split
                for (Multimap<VarKey, Sort> elem : vars) { // for every local type restrictions
                    for (Multimap<VarKey, Sort> elem2 : viz.vars) { // create a combination with every ambiguity detected
                        Multimap<VarKey, Sort> clone = HashMultimap.create();
                        clone.putAll(elem);
                        clone.putAll(elem2);
                        newVars.add(clone);
                    }
                }
                if (vars.size() == 0)
                    newVars.addAll(viz.vars);
            }
            if (!newVars.isEmpty())
                vars = newVars;
            return node;
        }

        public Term apply(TermCons tc) {
            if (tc.production().klabel().isDefined()
                    && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                    || tc.production().klabel().get().name().equals("#InnerCast"))) {
                Term t = tc.get(0);
                new CollectUndeclaredVariables2(getSortOfCast(tc)).apply(t);
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.get(j);
                        new CollectUndeclaredVariables2(((NonTerminal) tc.production().items().apply(i)).sort()).apply(t);
                        j++;
                    }
                }
            }
            return super.apply(tc);
        }

        private class CollectUndeclaredVariables2 extends SafeTransformer {
            private final Sort sort;
            public CollectUndeclaredVariables2(Sort sort) {
                this.sort = sort;
            }

            public Term apply(TermCons tc) {
                if (tc.production().att().contains("bracket")
                        || (tc.production().klabel().isDefined()
                        && tc.production().klabel().get().equals(KLabel("#KRewrite")))) {
                    return super.apply(tc);
                }
                return tc;
            }

            public Term apply(Constant c) {
                if (c.production().sort().equals(Sorts.KVariable()) && !declaredNames.contains(getVarKey(c))) {
                    if (vars.isEmpty())
                        vars.add(HashMultimap.<VarKey, Sort>create());
                    for (Multimap<VarKey, Sort> vars2 : vars)
                        vars2.put(getVarKey(c), sort);
                }

                return c;
            }
        }
    }
}

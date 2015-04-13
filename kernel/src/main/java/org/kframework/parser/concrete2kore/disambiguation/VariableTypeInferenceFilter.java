// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.compile.utils.MetaK;
import org.kframework.kore.Sort;
import org.kframework.definition.NonTerminal;
import org.kframework.parser.Constant;
import org.kframework.parser.SetsGeneralTransformer;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.*;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.VariableTypeClashException;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

/**
 * Apply the priority and associativity filters.
 */
public class VariableTypeInferenceFilter extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {
    public enum VarType { CONTEXT, USER }
    private final POSet<Sort> subsorts;
    private final scala.collection.immutable.Set<Sort> sortSet;
    private Set<ParseFailedException> warnings = this.warningUnit();
    public VariableTypeInferenceFilter(POSet<Sort> subsorts, scala.collection.immutable.Set<Sort> sortSet) {
        this.subsorts = subsorts;
        this.sortSet = sortSet;
    }

    @Override
    public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<ParseFailedException>> apply(Term t) {

        Set<VarInfo> vis = new CollectVariables().apply(t)._2();
        //System.out.println("vis = " + vis);
        Map<String, Sort> decl = new HashMap<>();
        for (VarInfo vi : vis) {
            Sort s = decl.get(vi.varName);
            if (vi.varType == VarType.USER) {
                if (s == null) {
                    decl.put(vi.varName, vi.sort);
                } else if (!s.equals(vi.sort)) {
                    String msg = vi.varName + " declared with two different sorts: " + s + " and " + vi.sort;
                    //System.out.println(msg);
                    KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, t.source().get(), t.location().get());
                    return new Tuple2<>(Left.apply(Sets.newHashSet(new VariableTypeClashException(kex))), this.warningUnit());
                }
            }
        }

        //System.out.println("decl = " + decl);
        Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck(decl).apply(t);
        if (rez.isLeft())
            return Tuple2.apply(rez, this.warningUnit());
        else
            t = rez.right().get();

        boolean varTypeInference = true;
        if (varTypeInference) {
            CollectExpectedVariablesVisitor vars2 = new CollectExpectedVariablesVisitor(decl.keySet());
            vars2.apply(t);
            //System.out.println("vars = " + vars2.vars);

            Set<Multimap<String, Sort>> solutions = new HashSet<>();
            String fails = null;
            Set<Sort> failsAmb = null;
            String failsAmbName = null;
            for (Multimap<String, Sort> variant : vars2.vars) {
                // take each solution and do GLB on every variable
                Multimap<String, Sort> solution = HashMultimap.create();
                for (String key : variant.keySet()) {
                    Collection<Sort> values = variant.get(key);
                    Set<Sort> mins = new HashSet<>();
                    for (Sort sort : iterable(sortSet)) { // for every declared sort
                        if (subsorts.lessThenEq(sort, Sort("KBott")))
                            continue;
                        boolean min = true;
                        for (Sort var : values) {
                            if (!subsorts.greaterThenEq(var, sort)) {
                                min = false;
                                break;
                            }
                        }
                        if (min)
                            mins.add(sort);
                    }
                    if (mins.size() == 0) {
                        fails = key;
                        solution.clear();
                        break;
                    } else if (mins.size() > 1) {
                        java.util.Set<Sort> maxSorts = new HashSet<>();

                        for (Sort vv1 : mins) {
                            boolean maxSort = true;
                            for (Sort vv2 : mins)
                                if (subsorts.lessThen(vv1, vv2))
                                    maxSort = false;
                            if (maxSort)
                                maxSorts.add(vv1);
                        }

                        if (maxSorts.size() == 1)
                            solution.putAll(key, maxSorts);
                        else {
                            failsAmb = maxSorts;
                            failsAmbName = key;
                            solution.clear();
                            break;
                        }
                    } else {
                        solution.putAll(key, mins);
                    }
                }
                // I found a solution that fits everywhere, then store it for disambiguation
                if (!solution.isEmpty())
                    solutions.add(solution);
            }
            if (!vars2.vars.isEmpty()) {
                if (solutions.size() == 0) {
                    if (fails != null) {
                        String msg = "Could not infer a sort for variable '" + fails + "' to match every location.";
                        KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, t.source().get(), t.location().get());
                        return new Tuple2<>(Left.apply(Sets.newHashSet(new VariableTypeClashException(kex))), this.warningUnit());

                    } else {
                        // Failure when in the same solution I can't find a unique sort for a specific variable.
                        String msg = "Could not infer a unique sort for variable '" + failsAmbName + "'.";
                        msg += " Possible sorts: ";
                        for (Sort vv1 : failsAmb)
                            msg += vv1 + ", ";
                        msg = msg.substring(0, msg.length() - 2);
                        KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, t.source().get(), t.location().get());
                        return new Tuple2<>(Left.apply(Sets.newHashSet(new VariableTypeClashException(kex))), this.warningUnit());

                    }
                } else if (solutions.size() == 1) {
                    //System.out.println("solutions = " + solutions);
                    Multimap<String, Sort> sol1 = solutions.iterator().next();
                    decl.clear();
                    for (String key : sol1.keySet()) {
                        Sort sort = sol1.get(key).iterator().next();
                        decl.put(key, sort);
                        String msg = "Variable '" + key + "' was not declared. Assuming sort " + sort + ".";
                        warnings = mergeWarnings(warnings, makeWarningSet(new VariableTypeClashException(
                                new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.COMPILER, msg, t.source().get(), t.location().get()))));
                    }
                    // after type inference for concrete sorts, reject erroneous branches
                    if (!decl.isEmpty()) {
                        t = new ApplyTypeCheck(decl).apply(t).right().get();
                    }
                } else {
                    Multimap<String, Sort> collect = HashMultimap.create();
                    for (Multimap<String, Sort> sol : solutions) {
                        collect.putAll(sol);
                    }
                    for (String key : collect.keySet()) {
                        Collection<Sort> values = collect.get(key);
                        if (values.size() > 1) {
                            String msg = "Could not infer a unique sort for variable '" + key + "'.";
                            msg += " Possible sorts: ";
                            for (Sort vv1 : values)
                                msg += vv1 + ", ";
                            msg = msg.substring(0, msg.length() - 2);
                            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, t.source().get(), t.location().get());
                            return new Tuple2<>(Left.apply(Sets.newHashSet(new VariableTypeClashException(kex))), this.warningUnit());
                        }
                    }
                    // The above loop looks for variables that can have multiple sorts, collected from multiple solutions.
                    // In rare cases (couldn't think of one right now) it may be that the
                    // solution may be different because of different variable names

                    // Ok, I found one example now. In C with unified-builtins, the follow restriction for ==Set doesn't work
                    // and it creates multiple parses with different amounts of variables
                    // This makes it that I can't disambiguate properly
                    // I can't think of a quick fix... actually any fix. I will delay it for the new parser.
                    String msg = "Parser: failed to infer sorts for variables.\n    Please file a bug report at https://github.com/kframework/k/issues.";
                    KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, t.source().get(), t.location().get());
                    return new Tuple2<>(Left.apply(Sets.newHashSet(new VariableTypeClashException(kex))), this.warningUnit());
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
        public String varName;
        public Sort sort;
        public Location loc;
        public VarType varType;

        public VarInfo(String varName, Sort sort, Source source, Location loc, VarType varType) {
            this.varName = varName;
            this.sort = sort;
            this.loc = loc;
            this.varType = varType;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof VarInfo)) return false;

            VarInfo varInfo = (VarInfo) o;

            if (!loc.equals(varInfo.loc)) return false;
            if (!sort.equals(varInfo.sort)) return false;
            if (!varName.equals(varInfo.varName)) return false;
            if (varType != varInfo.varType) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = varName.hashCode();
            result = 31 * result + sort.hashCode();
            result = 31 * result + loc.hashCode();
            result = 31 * result + varType.hashCode();
            return result;
        }

        @Override
        public String toString() {
            return "VarInfo{" +
                    "'" + varName + '\'' +
                    ", " + sort +
                    ", " + loc +
                    ", " + varType +
                    '}';
        }
    }

    private static Sort getSortOfCast(TermCons tc) {
        switch (tc.production().klabel().get().name()) {
        case "#SyntacticCast":
        case "#SemanticCast":
        case "#OuterCast":
            return tc.production().sort();
        case "#InnerCast":
            return ((NonTerminal)tc.production().items().apply(0)).sort();
        default:
            throw new AssertionError("Unexpected cast type");
        }
    }

    private class CollectVariables extends SetsGeneralTransformer<ParseFailedException, VarInfo> {
        public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> apply(TermCons tc) {
            // TODO: (Radu) if this is cast, take the sort from annotations?
            Set<VarInfo> collector = this.makeWarningSet();
            if (tc.production().klabel().isDefined()
                    && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().equals("#SemanticCast")
                    || tc.production().klabel().get().name().equals("#InnerCast"))) {
                Term t = tc.get(0);
                collector = new CollectVariables2(getSortOfCast(tc), VarType.USER).apply(t)._2();
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.get(j);
                        Set<VarInfo> vars = new CollectVariables2(((NonTerminal) tc.production().items().apply(i)).sort(), VarType.CONTEXT).apply(t)._2();
                        collector = mergeWarnings(collector, vars);
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
                return new Tuple2<>(Right.apply(tc), this.warningUnit());
            }

            public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> apply(Constant c) {
                if (c.production().sort().name().equals("KVariable") && !c.value().equals(MetaK.Constants.anyVarSymbol)) {
                    return new Tuple2<>(Right.apply(c), this.makeWarningSet(new VarInfo(c.value(), this.sort, c.source().get(), c.location().get(), varType)));
                }
                return new Tuple2<>(Right.apply(c), this.warningUnit());
            }
        }
    }

    private class ApplyTypeCheck extends SetsTransformerWithErrors<ParseFailedException> {
        private final Map<String, Sort> decl;
        public ApplyTypeCheck(Map<String, Sort> decl) {
            this.decl = decl;
        }

        public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
            // TODO: (Radu) if this is cast, take the sort from annotations?
            if (tc.production().klabel().isDefined()
                    && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().equals("#SemanticCast")
                    || tc.production().klabel().get().name().equals("#InnerCast"))) {
                Term t = tc.get(0);
                Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck2(getSortOfCast(tc)).apply(t);
                if (rez.isLeft())
                    return rez;
                tc = tc.with(0, rez.right().get());
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.get(j);
                        Sort s = ((NonTerminal) tc.production().items().apply(i)).sort();
                        Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck2(s).apply(t);
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
            public ApplyTypeCheck2(Sort sort) {
                this.sort = sort;
            }

            // TODO (Radu): check types of terms under rewrites too?
            public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
                if (tc.production().att().contains("bracket")
                        || (tc.production().klabel().isDefined()
                        && tc.production().klabel().get().equals(KLabel("#KRewrite")))) {
                    return super.apply(tc);
                }
                return Right.apply(tc);
            }

            public Either<java.util.Set<ParseFailedException>, Term> apply(Constant c) {
                if (c.production().sort().name().equals("KVariable")) {
                    Sort declared = decl.get(c.value());
                    if (declared != null && !declared.equals(Sort("K"))) {
                        //System.out.println("c = " + c.value() + ", " + declared + " < " + sort);
                        if (!subsorts.lessThenEq(declared, sort)) {
                            // TODO: location information
                            String msg = "Unexpected sort " + declared + " for term " + c.value() + ". Expected " + sort + ".";
                            //System.out.println(msg);
                            KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, c.source().get(), c.location().get());
                            return Left.apply(Sets.newHashSet(new VariableTypeClashException(kex)));
                        }
                    }
                }
                return Right.apply(c);
            }
        }
    }

    public class CollectExpectedVariablesVisitor extends SafeTransformer {
        /**
         * Each element in the list is a Mapping from variable name and a list of constraints for that variable.
         * On each Ambiguity node, a cartesian product is created between the current List and each ambiguity variant.
         */
        public Set<Multimap<String, Sort>> vars = new HashSet<>();
        private final Set<String> declaredNames;

        public CollectExpectedVariablesVisitor(Set<String> declaredNames) {
            this.declaredNames = declaredNames;
        }

        @Override
        public Term apply(Ambiguity node) {
            Set<Multimap<String, Sort>> newVars = new HashSet<>();
            for (Term t : node.items()) {
                CollectExpectedVariablesVisitor viz = new CollectExpectedVariablesVisitor(declaredNames);
                viz.apply(t);
                // create the split
                for (Multimap<String, Sort> elem : vars) { // for every local type restrictions
                    for (Multimap<String, Sort> elem2 : viz.vars) { // create a combination with every ambiguity detected
                        Multimap<String, Sort> clone = HashMultimap.create();
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
            // TODO: (Radu) if this is cast, take the sort from annotations?
            if (tc.production().klabel().isDefined()
                    && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().equals("#SemanticCast")
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
                if (c.production().sort().name().equals("KVariable") && !declaredNames.contains(c.value()) && !c.value().equals(MetaK.Constants.anyVarSymbol)) {
                    if (vars.isEmpty())
                        vars.add(HashMultimap.<String, Sort>create());
                    for (Multimap<String, Sort> vars2 : vars)
                        vars2.put(c.value(), sort);
                }

                return c;
            }
        }
    }
}

// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.compile.utils.MetaK;
import org.kframework.kore.Sort;
import org.kframework.kore.outer.NonTerminal;
import org.kframework.parser.Constant;
import org.kframework.parser.Location;
import org.kframework.parser.SetsGeneralTransformer;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.*;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.VariableTypeClashException;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static org.kframework.kore.Constructors.*;

/**
 * Apply the priority and associativity filters.
 */
public class VariableTypeInferenceFilter extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {
    public enum VarType { CONTEXT, USER }
    private final POSet<Sort> subsorts;
    public VariableTypeInferenceFilter(POSet<Sort> subsorts) {
        this.subsorts = subsorts;
    }

    @Override
    public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<ParseFailedException>> apply(Term t) {

        Set<VarInfo> vis = new CollectVariables().apply(t)._2();
        System.out.println("vis = " + vis);
        Map<String, Sort> decl = new HashMap<>();
        for (VarInfo vi : vis) {
            Sort s = decl.get(vi.varName);
            if (vi.varType == VarType.USER) {
                if (s == null) {
                    decl.put(vi.varName, vi.sort);
                } else if (!s.equals(vi.sort)) {
                    String msg = vi.varName + " declared with two different sorts: " + s + " and " + vi.sort;
                    System.out.println(msg);
                    KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, null, null);
                    return new Tuple2<>(Left.apply(Sets.newHashSet(new VariableTypeClashException(kex))), this.warningUnit());
                }
            }
        }

        System.out.println("decl = " + decl);
        Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck(decl).apply(t);
        if (rez.isLeft())
            return Tuple2.apply(rez, this.warningUnit());
        else
            t = rez.right().get();

        // TODO: (Radu) do type inference for the variables which are left.
        CollectExpectedVariablesVisitor vars = new CollectExpectedVariablesVisitor(decl.keySet());
        vars.apply(t);
        System.out.println("vars = " + vars.vars);

        return new Tuple2<>(Right.apply(t), this.warningUnit());
    }

    private class VarInfo {
        public String varName;
        public Sort sort;
        public Location loc;
        public VarType varType;

        public VarInfo(String varName, Sort sort, Location loc, VarType varType) {
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

    private class CollectVariables extends SetsGeneralTransformer<ParseFailedException, VarInfo> {
        public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> apply(TermCons tc) {
            // TODO: (Radu) if this is cast, take the sort from annotations?
            Set<VarInfo> collector = this.makeWarningSet();
            if (tc.production().klabel().isDefined()
                    && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().equals("#SemanticCast")
                    || tc.production().klabel().get().name().equals("#InnerCast"))) {
                Term t = tc.items().get(0);
                collector = new CollectVariables2(Sort(tc.production().att().getString("sort").get()), VarType.USER).apply(t)._2();
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.items().get(j);
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
                if (c.production().sort().name().equals("KVariable")) {
                    return new Tuple2<>(Right.apply(c), this.makeWarningSet(new VarInfo(c.value(), this.sort, c.location().get(), varType)));
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
                Term t = tc.items().get(0);
                Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck2(Sort(tc.production().att().getString("sort").get())).apply(t);
                if (rez.isLeft())
                    return rez;
                tc.items().set(0, rez.right().get());
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.items().get(j);
                        Sort s = ((NonTerminal) tc.production().items().apply(i)).sort();
                        Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck2(s).apply(t);
                        if (rez.isLeft())
                            return rez;
                        tc.items().set(j, rez.right().get());
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
                        System.out.println("c = " + c.value() + ", " + declared + " < " + sort);
                        if (!subsorts.lessThenEq(declared, sort)) {
                            // TODO: location information
                            String msg = "Unexpected sort " + declared + " for term " + c.value() + ". Expected " + sort + ".";
                            System.out.println(msg);
                            KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, null, null);
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
                Term t = tc.items().get(0);
                new CollectUndeclaredVariables2(Sort(tc.production().att().getString("sort").get())).apply(t);
            } else {
                for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                    if (tc.production().items().apply(i) instanceof NonTerminal) {
                        Term t = tc.items().get(j);
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

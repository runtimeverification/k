// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import org.kframework.kore.outer.NonTerminal;
import org.kframework.parser.Constant;
import org.kframework.parser.Location;
import org.kframework.parser.SetsGeneralTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Function0;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Right;

import java.util.Set;

import static org.kframework.kore.Constructors.KLabel;
import static org.kframework.Collections.*;

/**
 * Apply the priority and associativity filters.
 */
public class VariableTypeInferenceFilter extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {

    @Override
    public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<ParseFailedException>> apply(Term t) {

        Set<VarInfo> vis = new CollectVariables().apply(t)._2();
        System.out.println("vis = " + vis);

        return new Tuple2<>(Right.apply(t), this.warningUnit());
    }

    private class VarInfo {
        public String varName;
        public Sort sort;
        public Location loc;

        public VarInfo(String varName, Sort sort, Location loc) {
            this.varName = varName;
            this.sort = sort;
            this.loc = loc;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            VarInfo varInfo = (VarInfo) o;

            if (!loc.equals(varInfo.loc)) return false;
            if (!sort.equals(varInfo.sort)) return false;
            if (!varName.equals(varInfo.varName)) return false;

            return true;
        }

        @Override
        public String toString() {
            return "VarInfo{" +
                    "varName='" + varName + '\'' +
                    ", sort=" + sort +
                    ", loc=" + loc +
                    '}';
        }

        @Override
        public int hashCode() {
            int result = loc.hashCode();
            result = 31 * result + varName.hashCode();
            result = 31 * result + sort.hashCode();
            return result;
        }
    }

    private class CollectVariables extends SetsGeneralTransformer<ParseFailedException, VarInfo> {
        public Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> apply(TermCons tc) {
            // TODO: if this is cast, take the sort from annotations
            Set<VarInfo> collector = this.makeWarningSet();
            for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
                if (tc.production().items().apply(i) instanceof NonTerminal) {
                    Term t = tc.items().get(j);
                    Set<VarInfo> vars = new CollectVariables2(((NonTerminal) tc.production().items().apply(i)).sort()).apply(t)._2();
                    collector = mergeWarnings(collector, vars);
                    j++;
                }
            }
            Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<VarInfo>> rez = super.apply(tc);
            return new Tuple2<>(Right.apply(rez._1().right().get()), mergeWarnings(collector, rez._2()));
        }

        private class CollectVariables2 extends SetsGeneralTransformer<ParseFailedException, VarInfo> {
            private final Sort sort;
            public CollectVariables2(Sort sort) {
                this.sort = sort;
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
                    return new Tuple2<>(Right.apply(c), this.makeWarningSet(new VarInfo(c.value(), this.sort, c.location().get())));
                }
                return new Tuple2<>(Right.apply(c), this.warningUnit());
            }
        }
    }
}

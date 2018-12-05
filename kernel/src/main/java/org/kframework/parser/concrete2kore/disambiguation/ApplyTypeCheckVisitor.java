// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.kil.Attribute;
import org.kframework.kore.Sort;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.VariableTypeClashException;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.Set;


public class ApplyTypeCheckVisitor extends SetsTransformerWithErrors<ParseFailedException> {
    private final POSet<Sort> subsorts;

    public ApplyTypeCheckVisitor(POSet<Sort> subsorts) {
        this.subsorts = subsorts;
    }

    public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
        for (int i = 0, j = 0; i < tc.production().items().size(); i++) {
            if (tc.production().items().apply(i) instanceof NonTerminal) {
                if (tc.production().klabel().isDefined()
                        && (tc.production().klabel().get().name().equals("#SyntacticCast")
                        || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                        || tc.production().klabel().get().name().equals("#InnerCast"))
                        || (VariableTypeInferenceFilter.isFunctionRule(tc) && j == 0)) {
                    Term t = tc.get(0);
                    boolean strict = tc.production().klabel().get().name().equals("#SyntacticCast") || tc.production().klabel().get().name().equals("#InnerCast");
                    Either<Set<ParseFailedException>, Term> rez = new ApplyTypeCheck2(VariableTypeInferenceFilter.getSortOfCast(tc), strict).apply(t);
                    if (rez.isLeft())
                        return rez;
                    tc = tc.with(0, rez.right().get());
                    j++;
                } else {
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
        private final boolean strict;
        public ApplyTypeCheck2(Sort sort) {
            this.sort = sort;
            strict = false;
        }

        public ApplyTypeCheck2(Sort sort, boolean strict) {
            this.sort = sort;
            this.strict = strict;
        }

        public Either<java.util.Set<ParseFailedException>, Term> apply(ProductionReference pr) {
            if (pr instanceof TermCons) {
                TermCons tc = (TermCons) pr;
                if (VariableTypeInferenceFilter.hasPolySort(tc)) {
                    return VariableTypeInferenceFilter.visitPolyChildren(tc, this::apply);
                }
            }
            if (pr instanceof Constant && pr.production().sort().equals(Sorts.KVariable())) {
                // skip variables since they will always have a different sort at this stage.
                return Right.apply(pr);
            }
            if ((!strict && !subsorts.lessThanEq(pr.production().sort(), sort)) || (strict && !pr.production().sort().equals(sort))) {
                String msg = "Unexpected sort " + pr.production().sort() + " for term parsed as production " + pr.production() + ". Expected " + sort + ".";
                KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, pr.source().orElse(null), pr.location().orElse(null));
                return Left.apply(Sets.newHashSet(new VariableTypeClashException(kex)));
            }

            return Right.apply(pr);
        }
    }
}

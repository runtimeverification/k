// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.kore.outer.NonTerminal;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.parser.TransformerWithErrors;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.PriorityException;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.LinkedHashSet;


/**
 * Make sure that KSequence binds greedy (has least priority after rewrite).
 */
public class CorrectKSeqPriorityVisitor extends TransformerWithErrors<java.util.Set<ParseFailedException>> {

    @Override
    public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;
        if (!tc.production().isSyntacticSubsort()
                && !tc.production().klabel().get().name().equals("#KRewrite")
                && !tc.production().klabel().get().name().equals("#KSequence")) {
            // match only on the outermost elements
            if (tc.production().items().head() instanceof NonTerminal) {
                Either<java.util.Set<ParseFailedException>, Term> rez =
                        new PriorityVisitor2().apply(tc.items().get(0));
                if (rez.isLeft())
                    return rez;
                tc.items().set(0, rez.right().get());
            }
            if (tc.production().items().last() instanceof NonTerminal) {
                int last = tc.items().size() - 1;
                Either<java.util.Set<ParseFailedException>, Term> rez =
                        new PriorityVisitor2().apply(tc.items().get(last));
                if (rez.isLeft())
                    return rez;
                tc.items().set(last, rez.right().get());
            }
        }
        return super.apply(tc);
    }

    private static class PriorityVisitor2 extends TransformerWithErrors<java.util.Set<ParseFailedException>> {
        public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
            // TODO: add location information
            if (tc.production().klabel().isDefined() && tc.production().klabel().get().name().equals("#KSequence")) {
                String msg = "Due to typing errors, => is not greedy. Use parentheses to set proper scope.";
                KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, null, null);
                return Left.apply(Sets.newHashSet(new PriorityException(kex)));
            }
            return Right.apply(tc);
        }

        public java.util.Set<ParseFailedException> mergeErrors(java.util.Set<ParseFailedException> a, java.util.Set<ParseFailedException> b) {
            return Sets.union(a, b);
        }

        @Override
        public java.util.Set<ParseFailedException> errorUnit() {
            return new LinkedHashSet<>();
        }
    }

    public java.util.Set<ParseFailedException> mergeErrors(java.util.Set<ParseFailedException> a, java.util.Set<ParseFailedException> b) {
        return Sets.union(a, b);
    }

    @Override
    public java.util.Set<ParseFailedException> errorUnit() {
        return new LinkedHashSet<>();
    }
}

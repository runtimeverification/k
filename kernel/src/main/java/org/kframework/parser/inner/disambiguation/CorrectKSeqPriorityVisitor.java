// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.Collections;
import org.kframework.definition.NonTerminal;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.Collections.*;

/**
 * Make sure that KSequence binds greedy (has least priority after rewrite).
 */
public class CorrectKSeqPriorityVisitor extends SetsTransformerWithErrors<KEMException> {

    private final static Set<String> exceptions;

    static {
        exceptions = new HashSet<>();
        exceptions.add("#ruleRequires");
        exceptions.add("#ruleEnsures");
        exceptions.add("#ruleRequiresEnsures");
        exceptions.add("#KRewrite");
        exceptions.add("#KSequence");
        exceptions.add("#KList");
    }

    @Override
    public Either<java.util.Set<KEMException>, Term> apply(Ambiguity amb) {
        // if the ambiguity has KSeq at the top, prefer them, and eliminate the rest
        scala.collection.immutable.Set<Term> rewrites = amb.items().stream().filter(o ->
                o instanceof TermCons &&
                        ((TermCons) o).production().klabel().isDefined() &&
                        ((TermCons) o).production().klabel().get().name().equals("#KSequence")).collect(Collections.toSet());
        if (rewrites.size() == 0 || rewrites.size() == amb.items().size())
            return super.apply(amb);
        if (rewrites.size() == 1)
            return Right.apply(rewrites.head());
        return super.apply(Ambiguity.apply(mutable(rewrites)));
    }

    @Override
    public Either<java.util.Set<KEMException>, Term> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;
        if (!tc.production().isSyntacticSubsort() && tc.production().klabel().isDefined()
                && !exceptions.contains(tc.production().klabel().get().name())) {
            // match only on the outermost elements
            if (tc.production().items().apply(0) instanceof NonTerminal) {
                Either<java.util.Set<KEMException>, Term> rez =
                        new PriorityVisitor2(tc).apply(tc.get(0));
                if (rez.isLeft())
                    return rez;
                tc = tc.with(0, rez.right().get());
            }
            if (tc.production().items().apply(tc.production().items().size() - 1) instanceof NonTerminal) {
                int last = tc.items().size() - 1;
                Either<java.util.Set<KEMException>, Term> rez =
                        new PriorityVisitor2(tc).apply(tc.get(last));
                if (rez.isLeft())
                    return rez;
                tc = tc.with(last, rez.right().get());
            }
        }
        return super.apply(tc);
    }

    private static class PriorityVisitor2 extends SetsTransformerWithErrors<KEMException> {
        private final TermCons parent;

        public PriorityVisitor2(TermCons parent) {
            this.parent = parent;
        }

        public Either<java.util.Set<KEMException>, Term> apply(TermCons tc) {
            if (tc.production().klabel().isDefined() && tc.production().klabel().get().name().equals("#KSequence")) {
                String msg = "~> is not allowed to be an immediate child of " + parent.production().klabel().get() +
                        "    Use parentheses: (x)~>(y) to set the proper scope of the operations.";
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
            }
            return Right.apply(tc);
        }
    }
}

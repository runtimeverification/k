// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.definition.NonTerminal;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;


/**
 * Make sure that KSequence binds greedy (has least priority after rewrite).
 */
public class CorrectCastPriorityVisitor extends SetsTransformerWithErrors<KEMException> {

    @Override
    public Either<java.util.Set<KEMException>, Term> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;
        if (!tc.production().isSyntacticSubsort()
                && tc.production().klabel().isDefined()
                && (tc.production().klabel().get().name().equals("#SyntacticCast")
                    || tc.production().klabel().get().name().startsWith("#SemanticCastTo"))) {
            // match only on the outermost elements
                Either<java.util.Set<KEMException>, Term> rez =
                        new PriorityVisitor2(tc).apply(tc.get(0));
                if (rez.isLeft())
                    return rez;
                tc = tc.with(0, rez.right().get());
        }
        return super.apply(tc);
    }

    private static class PriorityVisitor2 extends SetsTransformerWithErrors<KEMException> {
        private final TermCons parent;
        public PriorityVisitor2(TermCons parent) {
            this.parent = parent;
        }

        public Either<java.util.Set<KEMException>, Term> apply(TermCons tc) {
            if (tc.production().items().apply(tc.production().items().size() - 1) instanceof NonTerminal) {
                String msg = parent.production().klabel().get() + " is not allowed to be an immediate child of cast." +
                        "    Use parentheses: (x):Sort to set the proper scope of the operations.";
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
            }
            return Right.apply(tc);
        }
    }
}

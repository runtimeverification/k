// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Tag;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.PriorityException;
import scala.Tuple2;
import scala.collection.Set;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;


/**
 * Apply the priority and associativity filters.
 */
public class PriorityVisitor extends SetsTransformerWithErrors<ParseFailedException> {

    private final POSet<Tag> priorities;
    private final Set<Tuple2<Tag, Tag>> leftAssoc;
    private final Set<Tuple2<Tag, Tag>> rightAssoc;
    public PriorityVisitor(POSet<Tag> priorities, Set<Tuple2<Tag, Tag>> leftAssoc, Set<Tuple2<Tag, Tag>> rightAssoc) {
        super();
        this.priorities = priorities;
        this.leftAssoc = leftAssoc;
        this.rightAssoc = rightAssoc;
    }

    @Override
    public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;
        if (!tc.production().isSyntacticSubsort() && !tc.production().att().contains("bracket")) {
            // match only on the outermost elements
            if (tc.production().items().apply(0) instanceof NonTerminal) {
                Either<java.util.Set<ParseFailedException>, Term> rez =
                        new PriorityVisitor2(tc, PriorityVisitor2.Side.LEFT, priorities, leftAssoc, rightAssoc).apply(tc.get(0));
                if (rez.isLeft())
                    return rez;
                tc = tc.with(0, rez.right().get());
            }
            if (tc.production().items().apply(tc.production().items().size() - 1) instanceof NonTerminal) {
                int last = tc.items().size() - 1;
                Either<java.util.Set<ParseFailedException>, Term> rez =
                        new PriorityVisitor2(tc, PriorityVisitor2.Side.RIGHT, priorities, leftAssoc, rightAssoc).apply(tc.get(last));
                if (rez.isLeft())
                    return rez;
                tc = tc.with(last, rez.right().get());
            }
        }
        return super.apply(tc);
    }

    private static class PriorityVisitor2 extends SetsTransformerWithErrors<ParseFailedException> {
        /**
         * Specifies whether the current node is the left most or the right most child of the parent.
         * This is useful because associativity can be checked at the same time with priorities.
         */
        public static enum Side {LEFT, RIGHT}
        private final TermCons parent;
        private final Side side;
        private final POSet<Tag> priorities;
        private final Set<Tuple2<Tag, Tag>> leftAssoc;
        private final Set<Tuple2<Tag, Tag>> rigthAssoc;

        public PriorityVisitor2(TermCons parent, Side side, POSet<Tag> priorities, Set<Tuple2<Tag, Tag>> leftAssoc, Set<Tuple2<Tag, Tag>> rightAssoc) {
            this.parent = parent;
            this.side = side;
            this.priorities = priorities;
            this.leftAssoc = leftAssoc;
            this.rigthAssoc = rightAssoc;
        }

        public Either<java.util.Set<ParseFailedException>, Term> apply(TermCons tc) {
            if (tc.production().att().contains("bracket")) return Right.apply(tc);
            //if (Side.RIGHT  == side && !(tc.production().items().apply(0) instanceof NonTerminal)) return Right.apply(tc);
            //if (Side.LEFT == side && !(tc.production().items().apply(tc.production().items().size() - 1) instanceof NonTerminal)) return Right.apply(tc);
            Tag parentLabel = new Tag(parent.production().klabel().get().name());
            Tag localLabel = new Tag(tc.production().klabel().get().name());
            // TODO: add location information
            if (priorities.lessThen(parentLabel, localLabel)) {
                String msg = "Priority filter exception. Cannot use " + localLabel + " as a child of " + parentLabel;
                KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, tc.source().get(), tc.location().get());
                return Left.apply(Sets.newHashSet(new PriorityException(kex)));
            }
            if (leftAssoc.contains(new Tuple2<>(parentLabel, localLabel)) && Side.RIGHT == side) {
                String msg = "Associativity filter exception. Cannot use " + localLabel + " as a right child of " + parentLabel;
                KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, tc.source().get(), tc.location().get());
                return Left.apply(Sets.newHashSet(new PriorityException(kex)));
            }
            if (rigthAssoc.contains(new Tuple2<>(parentLabel, localLabel)) && Side.LEFT == side) {
                String msg = "Associativity filter exception. Cannot use " + localLabel + " as a left child of " + parentLabel;
                KException kex = new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, tc.source().get(), tc.location().get());
                return Left.apply(Sets.newHashSet(new PriorityException(kex)));
            }

            return Right.apply(tc);
        }
    }
}

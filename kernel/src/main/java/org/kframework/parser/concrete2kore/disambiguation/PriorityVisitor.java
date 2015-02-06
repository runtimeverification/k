// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.kore.outer.NonTerminal;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.parser.TranformerWithExceptionGathering;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.util.Either;

import java.util.Set;

/**
 * Apply the priority and associativity filters.
 */
public class PriorityVisitor extends TranformerWithExceptionGathering<ParseFailedException> {
    @Override
    public Either<Set<ParseFailedException>, Term> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;
        if (!tc.production().isSyntacticSubsort()) {
            // match only on the outermost elements
            if (tc.production().items().head() instanceof NonTerminal) {
                tc.items().set(0, new PriorityVisitor2(tc, PriorityVisitor2.Side.LEFT).apply(tc.items().get(0)).right().get());
            }
            if (tc.production().items().last() instanceof NonTerminal) {
                int last = tc.items().size() - 1;
                tc.items().set(last, new PriorityVisitor2(tc, PriorityVisitor2.Side.RIGHT).apply(tc.items().get(last)).right().get());
            }
        }
        return super.apply(tc);

/*        if (tc.getProduction().isListDecl()) {
            if (tc.getContents().size() == 2) { // I made the parser so it instantiates a TermCons
                // with 0 children if the list is empty. It also takes the place of the list terminator
                tc.getContents().set(0, (Term) new PriorityFilter2(tc, Side.LEFT, context).visitNode(tc.getContents().get(0)));
                tc.getContents().set(1, (Term) new PriorityFilter2(tc, Side.RIGHT, context).visitNode(tc.getContents().get(1)));
            }
        } else if (!tc.getProduction().isConstant() && !tc.getProduction().isSyntacticSubsort()) {
            for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
                if (tc.getProduction().getItems().get(i) instanceof NonTerminal) {
                    // look for the outermost element
                    if ((i == 0 || i == tc.getProduction().getItems().size() - 1)
                            && (tc.getContents().get(j) instanceof TermCons || tc.getContents().get(j) instanceof Ambiguity)) {
                        tc.getContents().set(j, (Term) new PriorityFilter2(tc,
                                i == 0 ? Side.LEFT : Side.RIGHT, context).visitNode(tc.getContents().get(j)));
                    }
                    j++;
                }
            }
        }

        return super.visit(tc, _void);
*/

/*
        List<Term> prefer = new ArrayList<>();
        List<Term> avoid = new ArrayList<>();
        for (Term t : amb.items()) {
            if (t instanceof ProductionReference) {
                if (((ProductionReference) t).production().att().contains("prefer")) {
                    prefer.add(t);
                } else if (((ProductionReference) t).production().att().contains("avoid")) {
                    avoid.add(t);
                }
            }
        }
        Term result = amb;

        if (!prefer.isEmpty()) {
            if (prefer.size() == 1) {
                result = prefer.get(0);
            } else {
                amb.replaceChildren(prefer);
            }
        } else if (!avoid.isEmpty()) {
            if (avoid.size() < amb.items().size()) {
                amb.items().removeAll(avoid);
                if (amb.items().size() == 1)
                    result = amb.items().iterator().next();
            }
        }

        Either<Set<ParseFailedException>, Term> vis;
        if (result instanceof Ambiguity) {
            // didn't manage to completely disambiguate, but I still need to go deeper into the tree
            return super.apply((Ambiguity) result);
        } else {
            // visit the preferred child
            return this.apply(result);
        }
        */
    }

    private static class PriorityVisitor2 extends TranformerWithExceptionGathering<ParseFailedException> {
        /**
         * Specifies whether the current node is the left most or the right most child of the parent.
         * This is useful because associativity can be checked at the same time with priorities.
         */
        public static enum Side {LEFT, RIGHT}
        private final TermCons parent;
        private final Side side;

        public PriorityVisitor2(TermCons parent, Side side) {
            this.parent = parent;
            this.side = side;
        }

        public Either<Set<ParseFailedException>, Term> apply(TermCons tc) {
/*            String parentLabel = parent.getProduction().getKLabel();
            String localLabel = tc.getProduction().getKLabel();
            if (context.isPriorityWrong(parentLabel, localLabel)) {
                String msg = "Priority filter exception. Cannot use " + localLabel + " as a child of " + parentLabel;
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getSource(), tc.getLocation());
                throw new PriorityException(kex);
            }
            if (context.isLeftAssoc(parentLabel, localLabel) && Side.RIGHT == side) {
                String msg = "Associativity filter exception. Cannot use " + localLabel + " as a right child of " + parentLabel;
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getSource(), tc.getLocation());
                throw new PriorityException(kex);
            }
            if (context.isRightAssoc(parentLabel, localLabel) && Side.LEFT == side) {
                String msg = "Associativity filter exception. Cannot use " + localLabel + " as a left child of " + parentLabel;
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getSource(), tc.getLocation());
                throw new PriorityException(kex);
            }

            return tc;
            */
            return super.apply(tc);
        }
    }
}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class PriorityFilter2 extends LocalTransformer {

    /**
     * Specifies whether the current node is the left most or the right most child of the parent.
     * This is useful because associativity can be checked at the same time with priorities.
     */
    public static enum Side {LEFT, RIGHT}
    private final TermCons parent;
    private final Side side;

    public PriorityFilter2(TermCons parent, Side side, Context context) {
        super("Type system2", context);
        this.parent = parent;
        this.side = side;
    }

    public PriorityFilter2(PriorityFilter2 pf, Context context) {
        super("Type system2", context);
        this.parent = pf.parent;
        this.side = pf.side;
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        String parentLabel = parent.getProduction().getKLabel();
        String localLabel = tc.getProduction().getKLabel();
        if (context.isPriorityWrong(parentLabel, localLabel)) {
            String msg = "Priority filter exception. Cannot use " + localLabel + " as a child of " + parentLabel;
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getFilename(), tc.getLocation());
            throw new PriorityException(kex);
        }
        if (context.isLeftAssoc(parentLabel, localLabel) && Side.RIGHT == side) {
            String msg = "Associativity filter exception. Cannot use " + localLabel + " as a right child of " + parentLabel;
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getFilename(), tc.getLocation());
            throw new PriorityException(kex);
        }
        if (context.isRightAssoc(parentLabel, localLabel) && Side.LEFT == side) {
            String msg = "Associativity filter exception. Cannot use " + localLabel + " as a left child of " + parentLabel;
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getFilename(), tc.getLocation());
            throw new PriorityException(kex);
        }

        return tc;
    }

    @Override
    public ASTNode visit(Ambiguity node, Void _) throws ParseFailedException {
        ParseFailedException exception = null;
        ArrayList<Term> terms = new ArrayList<Term>();
        for (Term t : node.getContents()) {
            ASTNode result = null;
            try {
                result = this.visitNode(t);
                terms.add((Term) result);
            } catch (ParseFailedException e) {
                exception = e;
            }
        }
        if (terms.isEmpty())
            throw exception;
        if (terms.size() == 1) {
            return terms.get(0);
        }
        node.setContents(terms);
        return node;
    }

    @Override
    public ASTNode visit(Term node, Void _) throws ParseFailedException {
        return node;
    }
}

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

    private TermCons parent;

    public PriorityFilter2(TermCons parent, Context context) {
        super("Type system", context);
        this.parent = parent;
    }

    public PriorityFilter2(PriorityFilter2 pf, Context context) {
        super("Type system", context);
        this.parent = pf.parent;
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

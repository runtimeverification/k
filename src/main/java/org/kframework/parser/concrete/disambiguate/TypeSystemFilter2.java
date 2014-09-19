// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.ArrayList;

public class TypeSystemFilter2 extends LocalTransformer {

    private Sort maxSort;
    // if true, reject anything which is not below maxSort, even K
    private final boolean strict;

    public TypeSystemFilter2(Sort maxSort, org.kframework.kil.loader.Context context) {
        super(TypeSystemFilter2.class.getName(), context);
        this.maxSort = maxSort;
        strict = false;
    }

    public TypeSystemFilter2(Sort maxSort, boolean strict, org.kframework.kil.loader.Context context) {
        super(TypeSystemFilter2.class.getName(), context);
        this.maxSort = maxSort;
        this.strict = strict;
    }

    public TypeSystemFilter2(TypeSystemFilter2 tsf, Context context) {
        super(TypeSystemFilter2.class.getName(), context);
        this.maxSort = tsf.maxSort;
        this.strict = tsf.strict;
    }

    @Override
    public ASTNode visit(Term trm, Void _) throws ParseFailedException {
        boolean error = false;
        if (strict && !trm.getSort().equals(maxSort))
            error = true;
        if ((!trm.getSort().equals(Sort.K) &&
             !trm.getSort().equals(Sort.KITEM) &&
             !trm.getSort().equals(Sort.KRESULT)))
            if (!context.isSyntacticSubsortedEq(maxSort, trm.getSort()))
                error = true;
        if (error) {
            KException kex = new KException(
                    ExceptionType.ERROR,
                    KExceptionGroup.CRITICAL,
                    "type error: unexpected term '" + trm + "' of sort '" + trm.getSort()
                            + "', expected sort '" + maxSort + "'.",
                    getName(),
                    trm.getSource(),
                    trm.getLocation());
            throw new ParseFailedException(kex);
        }
        return trm;
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
    public ASTNode visit(Bracket node, Void _) throws ParseFailedException {
        node.setContent((Term) this.visitNode(node.getContent()));
        return node;
    }

    @Override
    public ASTNode visit(Rewrite node, Void _) throws ParseFailedException {
        Rewrite result = new Rewrite(node);
        result.replaceChildren(
                (Term) this.visitNode(node.getLeft()),
                (Term) this.visitNode(node.getRight()),
                context);
        result.setSort(maxSort);
        // if the left hand side is a function, check to see if the right hand side has the same sort
        if (node.getLeft() instanceof TermCons && ((TermCons) node.getLeft()).getProduction().containsAttribute("function")) {
            TypeSystemFilter2 tsf = new TypeSystemFilter2(node.getLeft().getSort(), context);
            node.setRight((Term) tsf.visitNode(node.getRight()), context);
            result.setSort(node.getLeft().getSort());
        }

        return result;
    }
}

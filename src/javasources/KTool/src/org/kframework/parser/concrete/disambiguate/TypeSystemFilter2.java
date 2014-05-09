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

    private String maxSort;

    public TypeSystemFilter2(String maxSort, org.kframework.kil.loader.Context context) {
        super("Type system", context);
        this.maxSort = maxSort;
    }

    public TypeSystemFilter2(TypeSystemFilter2 tsf, Context context) {
        super("Type system", context);
        this.maxSort = tsf.maxSort;
    }

    @Override
    public ASTNode visit(Term trm, Void _) throws ParseFailedException {
        if (!trm.getSort().equals(KSorts.K) && !trm.getSort().equals(KSorts.KITEM)
                && !trm.getSort().equals(KSorts.KRESULT)) {
            if (!context.isSubsortedEq(maxSort, trm.getSort())) {
                KException kex = new KException(
                        ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL,
                        "type error: unexpected term '" + trm + "' of sort '" + trm.getSort()
                                + "', expected sort '" + maxSort + "'.",
                        trm.getFilename(),
                        trm.getLocation());
                throw new ParseFailedException(kex);
            }
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
        return result;
    }
}

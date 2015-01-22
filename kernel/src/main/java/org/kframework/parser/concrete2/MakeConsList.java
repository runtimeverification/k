// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Transforms a list with multiple elements into a sequence of constructors with only two or zero elements.
 */
public class MakeConsList extends ParseForestTransformer {

    public MakeConsList() {
        super(MakeConsList.class.getName(), null);
    }

    @Override
    public boolean cache() {
        return true;
    }

    @Override
    public ASTNode visit(TermCons tc, Void _void) throws ParseFailedException {
        if (tc.getProduction().isListDecl() && tc.getContents().size() > 0) {
            TermCons tail = new TermCons(tc);
            tail.getContents().remove(0);

            Term head = tc.getSubterm(0);
            tc.getContents().clear();
            tc.getContents().add(head);
            tc.getContents().add(tail);
        }
        return super.visit(tc, _void);
    }
}

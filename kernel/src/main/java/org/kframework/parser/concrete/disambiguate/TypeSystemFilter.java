// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cast;
import org.kframework.kil.Production;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;

public class TypeSystemFilter extends ParseForestTransformer {

    public TypeSystemFilter(Context context) {
        super("Type system", context);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _void) throws ParseFailedException {
        // choose only the allowed subsorts for a TermCons
        if (tc.getProduction().isListDecl()) {
            if (!tc.isListTerminator()) {
                UserList ulist = (UserList) tc.getProduction().getItems().get(0);
                tc.getContents().set(0, (Term) new TypeSystemFilter2(ulist.getSort(), context).visitNode(tc.getContents().get(0)));
                tc.getContents().set(1, (Term) new TypeSystemFilter2(tc.getProduction().getSort(), context).visitNode(tc.getContents().get(1)));
            }
        } else {
            int j = 0;
            Production prd = tc.getProduction();
            for (int i = 0; i < prd.getItems().size(); i++) {
                if (prd.getItems().get(i) instanceof NonTerminal) {
                    NonTerminal sort = (NonTerminal) prd.getItems().get(i);
                    Term child = tc.getContents().get(j);
                    tc.getContents().set(j, (Term) new TypeSystemFilter2(sort.getSort(), context).visitNode(child));
                    j++;
                }
            }
        }

        return super.visit(tc, _void);
    }

    @Override
    public ASTNode visit(Cast cast, Void _void) throws ParseFailedException {
        if (cast.getType() != Cast.CastType.OUTER)
            cast.setContent((Term) new TypeSystemFilter2(cast.getInnerSort(), true, context).visitNode(cast.getContent()));
        return super.visit(cast, _void);
    }
}

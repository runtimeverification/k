// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Collection;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.util.ArrayList;


public class FlattenListsFilter extends ParseForestTransformer {

    public FlattenListsFilter(Context context) {
        super("Flatten lists", context);
    }

    @Override
    public ASTNode visit(Collection c, Void _) throws ParseFailedException {
        boolean found;
        do {
            found = false;
            java.util.List<Term> contents = new ArrayList<Term>();
            for (Term t : c.getContents()) {
                if (t.getClass() == c.getClass()) {
                    found = true;
                    Collection c2 = (Collection) t;
                    contents.addAll(c2.getContents());
                } else
                    contents.add(t);
            }
            c.setContents(contents);
        } while (found);

        return super.visit(c, _);
    }
}

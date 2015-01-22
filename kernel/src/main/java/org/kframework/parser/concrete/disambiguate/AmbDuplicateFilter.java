// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.util.ArrayList;

public class AmbDuplicateFilter extends ParseForestTransformer {
    public AmbDuplicateFilter(Context context) {
        super("Remove ambiguity duplicates", context);
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _void) throws ParseFailedException {

        // remove duplicate ambiguities
        // should be applied after updating something like variable declarations
        java.util.List<Term> children = new ArrayList<Term>();
        for (Term t1 : amb.getContents()) {
            boolean unique = true;
            for (Term t2 : children)
                if (t1 != t2 && t1.equals(t2))
                    unique = false;
            if (unique)
                children.add(t1);
        }

        if (children.size() > 1) {
            amb.setContents(children);
            return super.visit(amb, _void);
        } else
            return super.visit(children.get(0), _void);
    }
}

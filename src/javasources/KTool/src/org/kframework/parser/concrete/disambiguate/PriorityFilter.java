// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;

public class PriorityFilter extends ParseForestTransformer {
    public PriorityFilter(Context context) {
        super("Priority filter", context);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        if (tc.getProduction() == null)
            System.err.println(this.getClass() + ":" + " cons not found." + tc.getCons());
        if (tc.getProduction().isListDecl()) {
            tc.getContents().set(0, (Term) new PriorityFilter2(tc, context).visitNode(tc.getContents().get(0)));
            tc.getContents().set(1, (Term) new PriorityFilter2(tc, context).visitNode(tc.getContents().get(1)));
        } else if (!tc.getProduction().isConstant() && !tc.getProduction().isSubsort()) {
            for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
                if (tc.getProduction().getItems().get(i) instanceof Sort) {
                    // look for the outermost element
                    if ((i == 0 || i == tc.getProduction().getItems().size() - 1)
                            && (tc.getContents().get(j) instanceof TermCons || tc.getContents().get(j) instanceof Ambiguity)) {
                        tc.getContents().set(j, (Term) new PriorityFilter2(tc, context).visitNode(tc.getContents().get(j)));
                    }
                    j++;
                }
            }
        }

        return super.visit(tc, _);
    }
}

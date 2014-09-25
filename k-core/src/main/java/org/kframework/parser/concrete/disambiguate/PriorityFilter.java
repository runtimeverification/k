// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.parser.concrete.disambiguate.PriorityFilter2.Side;

public class PriorityFilter extends ParseForestTransformer {
    public PriorityFilter(Context context) {
        super("Priority filter", context);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        assert tc.getProduction() != null : this.getClass() + ":" + " production not found." + tc;
        if (tc.getProduction().isListDecl()) {
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

        return super.visit(tc, _);
    }
}

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;

public class PreferAvoidFilter extends ParseForestTransformer {
    public PreferAvoidFilter(Context context) {
        super("Ambiguity filter", context);
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _) throws ParseFailedException {
        java.util.List<Term> prefer = new ArrayList<Term>();
        java.util.List<Term> avoid = new ArrayList<Term>();

        for (ASTNode variant : amb.getContents()) {
            if (variant instanceof TermCons) {
                TermCons tc = (TermCons) variant;
                if (tc.getProduction().containsAttribute("prefer"))
                    prefer.add(tc);
                if (tc.getProduction().containsAttribute("avoid"))
                    avoid.add(tc);
            } else if (variant instanceof KApp) {
                // Adding int tokens to the prefer container in order to disambiguate between
                // negative numbers and unary minus.
                KApp kapp = (KApp) variant;
                if (kapp.getLabel() instanceof IntBuiltin) {
                    prefer.add(kapp);
                }
            }
        }

        ASTNode result = amb;

        if (!prefer.isEmpty()) {
            if (prefer.size() == 1)
                result = prefer.get(0);
            else {
                amb.setContents(prefer);
            }
        } else if (!avoid.isEmpty()) {
            if (avoid.size() < amb.getContents().size()) {
                amb.getContents().removeAll(avoid);
                if (amb.getContents().size() == 1)
                    result = amb.getContents().get(0);
            }
        }

        if (result instanceof Ambiguity)
            // didn't manage to completely disambiguate, but I still need to go deeper into the tree
            return super.visit((Ambiguity) result, _);
        else
            // visit the preferred child
            return this.visitNode(result);
    }
}

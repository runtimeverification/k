// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.parser.Ambiguity;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;

import java.util.ArrayList;
import java.util.List;

/**
 * Apply the prefer/avoid disambiguation filter.
 * 1. match on an ambiguity node
 * 2. remove the productions that are labeled with 'avoid'
 * 3. keep only those productions which have 'prefer' (if any)
 */
public class PreferAvoidVisitor extends SafeTransformer {
    @Override
    public Term apply(Ambiguity amb) {
        List<Term> prefer = new ArrayList<>();
        List<Term> avoid = new ArrayList<>();
        for (Term t : amb.items()) {
            if (t instanceof ProductionReference) {
                if (((ProductionReference) t).production().att().contains("prefer")) {
                    prefer.add(t);
                } else if (((ProductionReference) t).production().att().contains("avoid")) {
                    avoid.add(t);
                }
            }
        }
        Term result = amb;

        if (!prefer.isEmpty()) {
            if (prefer.size() == 1) {
                result = prefer.get(0);
            } else {
                amb.replaceChildren(prefer);
            }
        } else if (!avoid.isEmpty()) {
            if (avoid.size() < amb.items().size()) {
                amb.items().removeAll(avoid);
                if (amb.items().size() == 1)
                    result = amb.items().iterator().next();
            }
        }

        if (result instanceof Ambiguity) {
            // didn't manage to completely disambiguate, but I still need to go deeper into the tree
            return super.apply((Ambiguity) result);
        } else {
            // visit the preferred child
            return this.apply(result);
        }
    }
}

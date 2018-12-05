// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.POSet;
import org.kframework.definition.Production;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.pcollections.PStack;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public class RemoveOverloads {
    private final POSet<Production> overloads;

    public RemoveOverloads(POSet<Production> overloads) {
        this.overloads = overloads;
    }

    public Term apply(Ambiguity a) {
        Set<Production> productions = new HashSet<>();
        for (Term t : a.items()) {
            if (t instanceof TermCons) {
                TermCons tc = (TermCons)t;
                productions.add(tc.production());
            } else {
                return a;
            }
        }
        Set<Production> candidates = overloads.minimal(productions);
        Ambiguity result = Ambiguity.apply(a.items().stream().filter(t -> candidates.contains(((ProductionReference)t).production())).collect(Collectors.toSet()));
        if (result.items().size() == 1) {
            return result.items().iterator().next();
        }
        return result;
    }
}

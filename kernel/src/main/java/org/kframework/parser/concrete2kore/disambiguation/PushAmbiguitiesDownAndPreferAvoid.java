// Copyright (c) 2017-2018 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.POSet;
import org.kframework.definition.Production;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by dwightguth on 5/3/17.
 */
public class PushAmbiguitiesDownAndPreferAvoid extends SafeTransformer {

    private POSet<Production> overloads;

    public PushAmbiguitiesDownAndPreferAvoid(POSet<Production> overloads) {
        this.overloads = overloads;
    }

    public Term preferAvoid(Ambiguity amb) {
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

        return result;
    }

    @Override
    public Term apply(Ambiguity a) {
        if (a.items().size() == 1)
            return apply(a.items().iterator().next());
        Production prod = null;
        int arity = 0;

        Term withoutOverloads = new RemoveOverloads(overloads).apply(a);
        if (!(withoutOverloads instanceof Ambiguity)) {
            return super.apply(withoutOverloads);
        }
        Term preferred = preferAvoid((Ambiguity)withoutOverloads);
        if (!(preferred instanceof Ambiguity)) {
            return super.apply(preferred);
        }
        a = (Ambiguity)preferred;

        a = (Ambiguity)super.apply(a);
        for (Term t : a.items()) {
            if (!(t instanceof ProductionReference)) {
                return a;
            }
            ProductionReference ref = (ProductionReference)t;
            if (prod == null) {
                prod = ref.production();
                if (ref instanceof TermCons) {
                    arity = ((TermCons) ref).items().size();
                }
            } else if (!prod.equals(ref.production())) {
                return a;
            }
        }
        if (arity == 0)
            return a;
        boolean[] same = new boolean[arity];
        for (int i = 0; i < arity; i++) {
            boolean sameAtIdx = true;
            Term sameTerm = null;
            for (Term t : a.items()) {
                TermCons tc = (TermCons)t;
                if (sameTerm == null) {
                    sameTerm = tc.get(i);
                } else if (!sameTerm.equals(tc.get(i))) {
                    sameAtIdx = false;
                }
            }
            same[i] = sameAtIdx;
        }
        TermCons first = (TermCons)a.items().iterator().next();
        for (int i = 0; i < arity; i++) {
            final int idx = i;
            boolean candidate = true;
            for (int j = 0; j < arity; j++) {
                if (i == j)
                    continue;
                if (!same[j]) {
                    candidate = false;
                    break;
                }
            }
            if (candidate) {
                return apply(first.with(i, new Ambiguity(a.items().stream().map(t -> (TermCons)t).map(t -> t.get(idx)).collect(Collectors.toSet()))));
            }
        }
        return a;
    }
}

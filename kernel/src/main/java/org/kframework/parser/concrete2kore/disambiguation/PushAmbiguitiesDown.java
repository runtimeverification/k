package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.definition.Production;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

import java.util.stream.Collectors;

/**
 * Created by dwightguth on 5/3/17.
 */
public class PushAmbiguitiesDown extends SafeTransformer {

    @Override
    public Term apply(Ambiguity a) {
        if (a.items().size() == 1)
            return apply(a.items().iterator().next());
        Production prod = null;
        int arity = 0;
        for (Term t : a.items()) {
            if (!(t instanceof ProductionReference)) {
                return super.apply(a);
            }
            ProductionReference ref = (ProductionReference)t;
            if (prod == null) {
                prod = ref.production();
                if (ref instanceof TermCons) {
                    arity = ((TermCons) ref).items().size();
                }
            } else if (!prod.equals(ref.production())) {
                return super.apply(a);
            }
        }
        if (arity == 0)
            return super.apply(a);
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
        return super.apply(a);
    }
}

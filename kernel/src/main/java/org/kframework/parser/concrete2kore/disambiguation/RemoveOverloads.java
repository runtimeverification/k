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

public class RemoveOverloads extends SafeTransformer {
    private final POSet<Production> overloads;

    public RemoveOverloads(POSet<Production> overloads) {
        this.overloads = overloads;
    }

    @Override
    public Term apply(Ambiguity a) {
        Term applied = super.apply(a);
        if (!(applied instanceof Ambiguity)) {
            return applied;
        }
        Ambiguity ambApplied = (Ambiguity) applied;
        PStack<Term> children = null;
        Set<Production> productions = new HashSet<>();
        for (Term t : ambApplied.items()) {
            if (t instanceof TermCons) {
                TermCons tc = (TermCons)t;
                productions.add(tc.production());
                if (children == null) {
                    children = tc.items();
                } else if (!children.equals(tc.items())) {
                    return applied;
                }
            } else {
                return applied;
            }
        }
        Set<Production> candidates = overloads.minimal(productions);
        Ambiguity result = Ambiguity.apply(ambApplied.items().stream().filter(t -> candidates.contains(((ProductionReference)t).production())).collect(Collectors.toSet()));
        if (result.items().size() == 1) {
            return result.items().iterator().next();
        }
        return result;
    }
}

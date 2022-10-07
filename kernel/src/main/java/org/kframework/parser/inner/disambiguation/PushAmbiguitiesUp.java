package org.kframework.parser.inner.disambiguation;

import org.kframework.parser.Ambiguity;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public class PushAmbiguitiesUp extends SafeTransformer {
    @Override
    public Term apply(TermCons tc) {
        for (int i = 0; i < tc.items().size(); i++) {
            tc = tc.with(i, apply(tc.get(i)));
        }
        for (int i = 0; i < tc.items().size(); i++) {
            if (tc.get(i) instanceof Ambiguity) {
                // If one of the children is an ambiguity,
                // push it up and reapply over the new ast
                Ambiguity old = (Ambiguity)tc.get(i);
                Set<Term> newTerms = new HashSet<>();
                for (Term child : old.items()) {
                    Term newTerm = apply(tc.with(i, apply(child)));
                    newTerms.add(newTerm);
                }
                return apply(Ambiguity.apply(newTerms));
            }
        }
        return tc;
    }

    @Override
    public Term apply(Ambiguity a) {
        a = a.replaceChildren(a.items().stream().map(t -> apply(t)).collect(Collectors.toList()));
        Set<Term> flatChildren = new HashSet<>();
        for (Term child : a.items()) {
            if (child instanceof Ambiguity) {
                Ambiguity ambChild = (Ambiguity)child;
                flatChildren.addAll(ambChild.items());
                continue;
            }
            flatChildren.add(child);
        }
        return Ambiguity.apply(flatChildren);
    }
}


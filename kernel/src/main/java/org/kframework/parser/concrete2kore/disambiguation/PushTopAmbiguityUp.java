// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import org.kframework.builtin.KLabels;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;

import java.util.HashSet;
import java.util.Set;

public class PushTopAmbiguityUp extends SafeTransformer {
    @Override
    public Term apply(TermCons tc) {
        if (tc.production().sort().name().equals("RuleContent")) {
            Term t = new PushTopAmbiguityUp2().apply(tc.get(0));
            if (t instanceof Ambiguity) {
                Ambiguity old = (Ambiguity)t;
                Set<Term> newTerms = new HashSet<>();
                for (Term child : old.items()) {
                    Term newTerm = tc.with(0, child);
                    newTerms.add(newTerm);
                }
                return Ambiguity.apply(newTerms);
            }
        }
        return super.apply(tc);
    }

    private class PushTopAmbiguityUp2 extends SafeTransformer {
        @Override
        public Term apply(TermCons tc) {
            if (tc.production().klabel().isDefined() && tc.production().klabel().get().equals(KLabels.KREWRITE)) {
                Term t = tc.get(0);
                if (t instanceof Ambiguity) {
                    Ambiguity old = (Ambiguity)t;
                    Set<Term> newTerms = new HashSet<>();
                    for (Term child : old.items()) {
                        Term newTerm = tc.with(0, child);
                        newTerms.add(newTerm);
                    }
                    return Ambiguity.apply(newTerms);
                }
            }
            return super.apply(tc);
        }
    }
}

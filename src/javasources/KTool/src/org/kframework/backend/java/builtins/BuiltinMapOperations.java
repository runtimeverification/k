package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


/**
 * Table of {@code public static} methods on builtin maps.
 *
 * @author AndreiS
 */
public class BuiltinMapOperations {

    public static BuiltinSet keys(BuiltinMap term, TermContext context) {
        if (!term.hasFrame()) {
            Set<Term> elements = new HashSet<Term>(term.getEntries().keySet());
            return new BuiltinSet(elements);
        } else {
            throw new IllegalArgumentException("argument " + term + " has frame");
        }
    }

    public static BuiltinMap construct(BuiltinMap term1, BuiltinMap term2, TermContext context) {
        Variable frame = null;
        if (term1.hasFrame() && term2.hasFrame()) {
            throw new IllegalArgumentException(
                    "both map arguments have frames, but the combined map cannot have two frames");
        } else if (term1.hasFrame()) {
            frame = term1.frame();
        } else if (term2.hasFrame()) {
            frame = term2.frame();
        }

        Map<Term, Term> entries = new HashMap<>(term1.getEntries());
        entries.putAll(term2.getEntries());
        return new BuiltinMap(entries, frame);

    }

    public static BuiltinMap update(BuiltinMap term, Term key, Term value, TermContext context) {
        if (!term.hasFrame()) {
            Map<Term, Term> entries = new HashMap<>(term.getEntries());
            entries.put(key, value);
            return new BuiltinMap(entries);
        } else {
            throw new IllegalArgumentException("argument " + term + " has frame");
        }
    }

}

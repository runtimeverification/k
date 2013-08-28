package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Term;

import java.util.HashSet;
import java.util.Set;


/**
 * Table of {@code public static} methods on builtin sets.
 *
 * @author AndreiS
 */
public class BuiltinMapOperations {

    public static BuiltinSet keys(BuiltinMap term) {
        if (!term.hasFrame()) {
            Set<Term> elements = new HashSet<Term>(term.getEntries().keySet());
            return new BuiltinSet(elements);
        } else {
            throw new IllegalArgumentException("argument " + term + " has frame");
        }

    }

}

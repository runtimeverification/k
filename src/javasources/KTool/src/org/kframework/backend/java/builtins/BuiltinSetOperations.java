package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Term;

import java.util.HashSet;
import java.util.Set;


/**
 * Table of {@code public static} methods on builtin sets.
 *
 * @author AndreiS
 */
public class BuiltinSetOperations {

    public static BuiltinSet difference(BuiltinSet term1, BuiltinSet term2) {
        if (!term1.isGround()) {
            throw new IllegalArgumentException("first argument " + term1 + " is not ground");
        }
        if (!term2.isGround()) {
            throw new IllegalArgumentException("second argument " + term2 + " is not ground");
        }

        Set<Term> elements = new HashSet<Term>(term1.elements());
        elements.removeAll(term2.elements());
        return new BuiltinSet(elements);
    }

    public static BoolToken in(Term term1, BuiltinSet term2) {
        if (!term1.isGround()) {
            throw new IllegalArgumentException("first argument " + term1 + " is not ground");
        }
        if (!term2.isGround()) {
            throw new IllegalArgumentException("second argument " + term2 + " is not ground");
        }

        return BoolToken.of(term2.elements().contains(term1));
    }

}

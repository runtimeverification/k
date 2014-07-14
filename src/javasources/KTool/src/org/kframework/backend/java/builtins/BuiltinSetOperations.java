// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.util.HashSet;
import java.util.Set;


/**
 * Table of {@code public static} methods on builtin sets.
 *
 * @author AndreiS
 */
public class BuiltinSetOperations {

    public static BuiltinSet construct(BuiltinSet term1, BuiltinSet term2, TermContext context) {
        Variable frame = null;
        if (term1.hasFrame() && term2.hasFrame()) {
            throw new IllegalArgumentException(
                    "both set arguments have frames, but the combined set cannot have two frames");
        } else if (term1.hasFrame()) {
            frame = term1.frame();
        } else if (term2.hasFrame()) {
            frame = term2.frame();
        }

        Set<Term> elements = new HashSet<>(term1.elements());
        elements.addAll(term2.elements());
        return new BuiltinSet(elements, frame);
    }

    public static BuiltinSet difference(BuiltinSet term1, BuiltinSet term2, TermContext context) {
        if (!term1.isGround() || !term2.isGround()) {
            return null;
        }

        Set<Term> elements = new HashSet<Term>(term1.elements());
        elements.removeAll(term2.elements());
        return new BuiltinSet(elements);
    }

    public static BoolToken in(Term term1, BuiltinSet term2, TermContext context) {
        if (!term1.isGround() || !term2.isGround()) {
            return null;
        }

        return BoolToken.of(term2.elements().contains(term1));
    }

}

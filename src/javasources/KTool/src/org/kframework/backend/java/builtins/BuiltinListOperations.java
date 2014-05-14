// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.util.ArrayList;
import java.util.List;


/**
 * Table of {@code public static} methods on builtin lists.
 *
 * @author AndreiS
 */
public class BuiltinListOperations {

    public static BuiltinList construct(BuiltinList term1, BuiltinList term2, TermContext context) {
        Variable frame = null;
        List<Term> elementsLeft = new ArrayList<>();
        List<Term> elementsRight = new ArrayList<>();
        if (term1.hasFrame() && term2.hasFrame()) {
            throw new IllegalArgumentException("both lists arguments have frames");
        } else if (term1.hasFrame()) {
            elementsLeft.addAll(term1.elementsLeft());
            frame = term1.frame();
            elementsRight.addAll(term1.elementsRight());
            elementsRight.addAll(term2.elementsLeft());
            elementsRight.addAll(term2.elementsRight());
        } else if (term2.hasFrame()) {
            elementsLeft.addAll(term1.elementsLeft());
            elementsLeft.addAll(term1.elementsRight());
            elementsLeft.addAll(term2.elementsLeft());
            frame = term2.frame();
            elementsRight.addAll(term2.elementsRight());
        } else {
            elementsLeft.addAll(term1.elementsLeft());
            elementsLeft.addAll(term1.elementsRight());
            elementsLeft.addAll(term2.elementsLeft());
            elementsLeft.addAll(term2.elementsRight());
        }
        return new BuiltinList(frame, 0, 0, elementsLeft, elementsRight);
    }

}

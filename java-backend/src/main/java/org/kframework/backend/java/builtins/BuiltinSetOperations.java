// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import com.google.common.collect.Sets;


/**
 * Table of {@code public static} methods on builtin sets.
 *
 * @author AndreiS
 */
public class BuiltinSetOperations {

    public static Term constructor(Term set1, Term set2, TermContext context) {
        if (set1.sort() != Sort.SET || set2.sort() != Sort.SET) {
            throw new IllegalArgumentException();
        }
        return BuiltinSet.concatenate(set1, set2);
    }

    public static Term unit(TermContext context) {
        return BuiltinSet.EMPTY_SET;
    }

    public static Term element(Term element, TermContext context) {
        BuiltinSet.Builder builder = BuiltinSet.builder();
        builder.add(element);
        return builder.build();
    }

    public static Term intersection(BuiltinSet set1, BuiltinSet set2, TermContext context) {
        if (!set1.isGround() || !set2.isGround()) {
            return null;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder();
        builder.addAll(Sets.intersection(set1.elements(), set2.elements()));
        return builder.build();
    }

    public static Term difference(BuiltinSet set1, BuiltinSet set2, TermContext context) {
        if (!set1.isGround() || !set2.isGround()) {
            return null;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder();
        builder.addAll(Sets.difference(set1.elements(), set2.elements()));
        return builder.build();
    }

    public static BoolToken in(Term element, BuiltinSet set, TermContext context) {
        if (set.contains(element)) {
            return BoolToken.TRUE;
        } else if (element.isGround() && set.isGround()) {
            return BoolToken.FALSE;
        } else if (set.isEmpty()) {
            return BoolToken.FALSE;
        } else {
            return null;
        }
    }

    public static BoolToken inclusion(BuiltinSet set1, BuiltinSet set2, TermContext context) {
        if (!set1.isGround() || !set2.isGround()) {
            return null;
        }

        return BoolToken.of(set2.elements().containsAll(set1.elements()));
    }

    public static Term choice(BuiltinSet set, TermContext context) {
        if (!set.elements().isEmpty()) {
            return set.elements().iterator().next();
        } else if (set.isEmpty()) {
            return Bottom.of(Kind.K);
        } else {
            return null;
        }
    }

}

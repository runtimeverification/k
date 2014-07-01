// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import com.google.common.base.Preconditions;

import java.util.HashSet;
import java.util.Set;


/**
 * Table of {@code public static} methods on builtin maps.
 *
 * @author AndreiS
 */
public class BuiltinMapOperations {

    public static BuiltinSet keys(BuiltinMap term, TermContext context) {
        Preconditions.checkArgument(!term.hasFrame(), "argument " + term + " has frame");
        
        Set<Term> elements = new HashSet<Term>(term.getEntries().keySet());
        return new BuiltinSet(elements);
    }

    public static Term construct(BuiltinMap term1, BuiltinMap term2, TermContext context) {
        return BuiltinMap.concatenate(term1, term2);
    }

    public static Term update(BuiltinMap term, Term key, Term value, TermContext context) {
        Preconditions.checkArgument(!term.hasFrame(), "argument " + term + " has frame");
        
        BuiltinMap.Builder builder = BuiltinMap.builder();
        builder.putAll(term.getEntries());
        builder.put(key, value);
        return builder.build();
    }

}

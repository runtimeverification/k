// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

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

    public static BuiltinMap construct(BuiltinMap term1, BuiltinMap term2, TermContext context) {
        Preconditions.checkArgument(!term1.hasFrame() || !term2.hasFrame(), 
                "both map arguments have frames, but the combined map cannot have two frames");
        
        Variable frame = null;
        if (term1.hasFrame()) {
            frame = term1.frame();
        } else if (term2.hasFrame()) {
            frame = term2.frame();
        }

        BuiltinMap.Builder builder = BuiltinMap.builder();
        builder.putAll(term1.getEntries());
        builder.putAll(term2.getEntries());
        builder.setFrame(frame);
        return builder.build();
    }

    public static BuiltinMap update(BuiltinMap term, Term key, Term value, TermContext context) {
        Preconditions.checkArgument(!term.hasFrame(), "argument " + term + " has frame");
        
        BuiltinMap.Builder builder = BuiltinMap.builder();
        builder.putAll(term.getEntries());
        builder.put(key, value);
        return builder.build();
    }

}

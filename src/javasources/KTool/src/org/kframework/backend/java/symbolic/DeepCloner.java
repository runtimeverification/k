// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Immutable;
import org.kframework.backend.java.kil.Term;

import com.rits.cloning.Cloner;

/**
 * Deep cloning utility class.
 * 
 * @author YilongL
 * 
 */
public class DeepCloner {
    
    private static final Cloner cloner = new Cloner();
    
    static {
        cloner.dontCloneInstanceOf(Immutable.class);
    }
            
    public static Term clone(Term term) {
        return cloner.deepClone(term);
    }
       
}

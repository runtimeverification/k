// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

/**
 * Interface for data structure choice operations.
 * 
 * @author YilongL
 *
 */
public interface DataStructureChoice extends DataStructureLookupOrChoice {
    
    enum Type { MAP_KEY_CHOICE, SET_ELEMENT_CHOICE }
    
    Term base();
    Term evaluateChoice();
    Type type();
}

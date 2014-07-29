// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * Interface for data structure lookup operations.
 *
 * @author YilongL
 *
 */
public interface DataStructureLookup extends DataStructureLookupOrChoice {

    enum Type { MAP_LOOKUP, LIST_LOOKUP, SET_LOOKUP }

    Term key();
    Term evaluateLookup();
    Type type();
}

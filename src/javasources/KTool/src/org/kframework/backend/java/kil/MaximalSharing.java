// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * The tag interface for maximally shared {@code Term}s. Maximally shared terms
 * are immutable; and there is at most one instance for each different maximally
 * shared terms. Therefore, equality check involving maximally shared term can
 * be done by identity check.
 * 
 * @author YilongL
 * 
 */
public interface MaximalSharing extends Immutable {
    
    // TODO(YilongL): maybe implement equals method here once we switch to Java 8 
}

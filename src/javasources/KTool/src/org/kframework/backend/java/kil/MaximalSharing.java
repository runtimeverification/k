// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * The tag interface for maximally shared objects. Maximally shared objects are
 * immutable; and there is at most one instance for each different maximally
 * shared objects. Therefore, equality check involving maximally shared object
 * can be done by identity check.
 *
 * @author YilongL
 *
 */
public interface MaximalSharing extends Immutable {

    // TODO(YilongL): maybe implement equals method here once we switch to Java 8

    // TODO(YilongL): enforce the overriding of readResolve method once we switch to java 8?
}

// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.transformation;

import com.google.inject.throwingproviders.CheckedProvider;

/**
 * A Guice throwing provider which provides a transformation.
 * @author dwightguth
 *
 * @param <T> The type of the transformation being provided
 */
public interface TransformationProvider<T> extends CheckedProvider<T> {

    /**
     * @return The implementation of the transformation being provided.
     * @throws TransformationNotSatisfiedException if no transformation
     * can be found which satisfies the input and output being requested.
     * @throws AmbiguousTransformationException if two or more transformations
     * could be found to transform the input term, and it cannot be determined
     * which should be used.
     */
    T get() throws TransformationNotSatisfiedException, AmbiguousTransformationException;
}

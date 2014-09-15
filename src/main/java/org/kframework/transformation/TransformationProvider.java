// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.transformation;

import com.google.inject.throwingproviders.CheckedProvider;

public interface TransformationProvider<T> extends CheckedProvider<T> {
    T get() throws TransformationNotSatisfiedException, AmbiguousTransformationException;
}

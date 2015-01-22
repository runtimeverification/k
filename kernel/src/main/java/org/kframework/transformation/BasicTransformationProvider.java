// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.transformation;

import com.google.inject.Inject;

/**
 * A basic implementation of the TransformationProvider interface.
 *
 * This is a replacement for the Providers.of method used for providers
 * which do not throw exceptions, adapted for use with throwing providers.
 * @author dwightguth
 *
 * @param <Interface> The interface which this instance should provide an implementation of
 * @param <Impl> The type of the implementation which should be provided.
 */
public class BasicTransformationProvider<Interface, Impl extends Interface> implements TransformationProvider<Interface> {

    private final Impl impl;

    @Inject
    public BasicTransformationProvider(
            Impl impl) {
        this.impl = impl;
    }

    @Override
    public Interface get() {
        return impl;
    }

}

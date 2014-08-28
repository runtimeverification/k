package org.kframework.transformation;

import com.google.inject.Inject;

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

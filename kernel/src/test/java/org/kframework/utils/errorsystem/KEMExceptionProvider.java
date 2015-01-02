// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.transformation.TransformationProvider;

public class KEMExceptionProvider<T> implements TransformationProvider<T> {

    @Override
    public T get() {
        throw KExceptionManager.criticalError("foo");
    }
}

// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.main.GlobalOptions;
import org.kframework.transformation.TransformationProvider;

public class KEMExceptionProvider<T> implements TransformationProvider<T> {

    @Override
    public T get() {
        new KExceptionManager(new GlobalOptions()).registerCriticalError("foo");
        throw new AssertionError("unreachable");
    }
}

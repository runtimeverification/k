// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.Provider;

public class NullProvider implements Provider<Object> {
    public Object get() {
        return null;
    };
}

// Copyright (C) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.loader.Context;


public class CopyOnWriteTransformer extends AbstractTransformer {

    public CopyOnWriteTransformer(String name, Context context) {
        super(name, context);
    }

    @Override
    public boolean visitChildren() {
        return true;
    }

    @Override
    public boolean copy() {
        return true;
    }
}

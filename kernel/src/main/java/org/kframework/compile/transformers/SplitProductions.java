// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * @author AndreiS
 */
public class SplitProductions extends CopyOnWriteTransformer {

    public SplitProductions(Context context) {
        super("", context);
    }
}

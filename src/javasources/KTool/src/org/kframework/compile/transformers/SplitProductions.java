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

// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class FlattenDisambiguationFilter extends CopyOnWriteTransformer {
    public FlattenDisambiguationFilter(Context context) {
        super("Reflatten ambiguous syntax", context);
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _void)  {
        // dwightguth: I don't think we actually need to flatten
        // syntax here; we can just pick one of the results at
        // random.

        return amb.getContents().get(0);
    }
}

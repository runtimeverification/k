// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.tags;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kompile.KompileOptions;

public class AddOptionalTags extends CopyOnWriteTransformer {

    private KompileOptions options;

    public AddOptionalTags(Context context) {
        super("AddOptionalTags", context);
        this.options = context.kompileOptions;
    }

    @Override
    public ASTNode visit(Attributes node, Void _) {

        for (String tag : options.transition)
            if (node.containsKey(tag))
                node.add(Attribute.TRANSITION);
        for (String tag : options.supercool)
            if (node.containsKey(tag))
                node.add(Attribute.SUPERCOOL);
        for (String tag : options.superheat)
            if (node.containsKey(tag))
                node.add(Attribute.SUPERHEAT);

        return node;
    }
}

// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.tags;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddDefaultComputational extends CopyOnWriteTransformer {

    public AddDefaultComputational(Context context) {
        super("AddDefaultComputational", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _void) {
        if (!(node.containsAttribute("structural")
                || node.containsAttribute(Attribute.ANYWHERE_KEY)
                || node.containsAttribute(Attribute.FUNCTION_KEY)
                || node.containsAttribute(Attribute.PREDICATE_KEY)))
            node.putAttribute("computational", "");

        return node;
    }
}

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.tags;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddStrictStar extends BasicTransformer {

    public AddStrictStar(Context context) {
        super("AddStrictStar", context);
    }

    @Override
    public ASTNode visit(Production node, Void _) throws TransformerException {
        if (node.containsAttribute("strict") || node.containsAttribute("seqstrict"))
            node.putAttribute("strict*", "");

        return node;
    }
}

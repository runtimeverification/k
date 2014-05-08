// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Bracket;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Delete Bracket nodes
 */
public class RemoveBrackets extends CopyOnWriteTransformer {

    public RemoveBrackets(Context context) {
        super("Remove brackets", context);
    }

    @Override
    public ASTNode visit(Bracket node, Void _)  {
        // System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
        return this.visitNode(node.getContent());
    }
}

// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Bracket;
import org.kframework.kil.TermCons;
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
    public ASTNode visit(Bracket node, Void _void)  {
        // System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
        return this.visitNode(node.getContent());
    }

    @Override
    public ASTNode visit(TermCons node, Void _void)  {
        // System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
        if (node.getProduction().containsAttribute("bracket"))
            return this.visitNode(node.getContents().get(0));
        return super.visit(node, _void);
    }
}

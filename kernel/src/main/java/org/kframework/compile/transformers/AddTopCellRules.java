// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;


public class AddTopCellRules extends CopyOnWriteTransformer {

    public AddTopCellRules(Context context) {
        super("Add top cell for rules", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _void) {
        if (MetaK.isAnywhere(node)) return node;
        if (!MetaK.hasCell(node.getBody(), context)) return node;
        node = node.shallowCopy();
        node.setBody(MetaK.wrap(node.getBody(),MetaK.Constants.generatedTopCellLabel,Ellipses.BOTH));
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _void) {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _void) {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _void) {
        return node;
    }

}

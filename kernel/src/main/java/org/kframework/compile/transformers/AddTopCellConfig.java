// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.ArrayList;
import java.util.List;


public class AddTopCellConfig extends CopyOnWriteTransformer {

    public AddTopCellConfig(Context context) {
        super("Add top cell for configurations", context);
    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
        ASTNode result = super.visit(node, _void);
        if (result == node) return node;
        if (result == null) {
            throw KExceptionManager.compilerError(
                    "Expecting Module, but got null. Returning the untransformed module.",
                    this, node);
        }
        if (!(result instanceof Module)) {
            throw KExceptionManager.internalError(
                    "Expecting Module, but got " + result.getClass() + " while transforming.",
                    this, node);
        }
        node = (Module) result;
        List<PriorityBlock> topCellBlocks = new ArrayList<PriorityBlock>();
        PriorityBlock topPriorityBlock = new PriorityBlock();
        List<ProductionItem> topTerminals = new ArrayList<ProductionItem>();
        topTerminals.add(new Terminal(MetaK.Constants.generatedTopCellLabel));
        Production topProduction = new Production(new NonTerminal(Sort.CELL_LABEL), topTerminals );
        topPriorityBlock.getProductions().add(topProduction);
        topCellBlocks.add(topPriorityBlock);
        return node;
    }

    @Override
    public ASTNode visit(Rule node, Void _void) {
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _void) {
        node = node.shallowCopy();
        node.setBody(MetaK.wrap(node.getBody(),MetaK.Constants.generatedTopCellLabel,Ellipses.NONE));
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

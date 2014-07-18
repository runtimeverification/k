// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.List;


public class AddTopCellConfig extends CopyOnWriteTransformer {

    public AddTopCellConfig(Context context) {
        super("Add top cell for configurations", context);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        ASTNode result = super.visit(node, _);
        if (result == node) return node;
        if (result == null) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.COMPILER,
                    "Expecting Module, but got null. Returning the untransformed module.",
                    getName(), node.getFilename(), node.getLocation()));
            return node;
        }
        if (!(result instanceof Module)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.INTERNAL,
                    "Expecting Module, but got " + result.getClass() + " while transforming.",
                    node.getFilename(), node.getLocation()));
            return node;
        }
        node = (Module) result;
        List<PriorityBlock> topCellBlocks = new ArrayList<PriorityBlock>();
        PriorityBlock topPriorityBlock = new PriorityBlock();
        List<ProductionItem> topTerminals = new ArrayList<ProductionItem>();
        topTerminals.add(new Terminal(MetaK.Constants.generatedTopCellLabel));
        Production topProduction = new Production(new Sort("CellLabel"), topTerminals );
        topPriorityBlock.getProductions().add(topProduction);
        topCellBlocks.add(topPriorityBlock);
        return node;
    }

    @Override
    public ASTNode visit(Rule node, Void _) {
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _) {
        node = node.shallowCopy();
        node.setBody(MetaK.wrap(node.getBody(),MetaK.Constants.generatedTopCellLabel,Ellipses.NONE));
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _) {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _) {
        return node;
    }

}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class AddStreamCells extends CopyOnWriteTransformer {

    List<Rule> generated = new ArrayList<Rule>();

    public AddStreamCells(Context context) {
        super("Add cells to stream rules", context);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        ASTNode result = super.visit(node, _);
        if (result == node)
            return node;
        if (generated.isEmpty()) {
//            GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER,
//                    "Stream cells missing in module " + node.getName() + ". " +
//                            "Some rules tagged with streams have been erased",
//                    node.getFilename(), node.getLocation()));
            return result;
        }
        result = result.shallowCopy();
        ((Module)result).getItems().addAll(generated);
        return result;
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }
    
    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }
    
    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }
    
    @Override
    public ASTNode visit(Rule node, Void _)  {
        boolean isStream = false;
        if (node.getAttributes().containsKey("stdin")) {
            isStream = true;
            addRules(node, "stdin");
        }
        if (node.getAttributes().containsKey("stdout")) {
            isStream = true;
            addRules(node, "stdout");
        }
        if (node.getAttributes().containsKey("stderr")) {
            isStream = true;
            addRules(node, "stderr");
        }
        if (isStream) {
            return null;
        }
        return node;
    }

    private void addRules(Rule rule, String stream) {
        DataStructureSort sort = context.dataStructureSortOf(rule.getBody().getSort());
        if (!(rule.getBody().getSort().equals("List") || rule.getBody().getSort().equals("ListItem") || context.dataStructureListSortOf(rule.getBody().getSort()) != null)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.INTERNAL,
                    "Found a rule tagged '" + stream + "' whose body wasn't a list.",
                        getName(), rule.getFilename(), rule.getLocation()));
        }
        Set<Cell> cells = new HashSet<Cell>();
        for (String cellName : context.cells.keySet()) {
            Cell cell = context.cells.get(cellName);
            if (stream.equals(cell.getCellAttributes().get("stream"))) {
                cells.add(cell);
            }
        }
        for (Cell cell : cells) {
            Rule newRule = rule.shallowCopy();
            Attributes newAttrs = newRule.getAttributes().shallowCopy();
            newAttrs.remove("function");
            newRule.setAttributes(newAttrs);
            newRule.setBody(MetaK.wrap(rule.getBody(), cell.getLabel(), Ellipses.NONE));
            generated.add(newRule);
        }
    }
}

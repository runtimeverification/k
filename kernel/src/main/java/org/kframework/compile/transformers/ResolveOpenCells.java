// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.ArrayList;
import java.util.HashMap;

public class ResolveOpenCells extends CopyOnWriteTransformer {

    public ResolveOpenCells(org.kframework.kil.loader.Context context) {
        super("Resolve Open Cells", context);
    }

    @Override
    public ASTNode visit(Cell node, Void _void)  {
        node = (Cell) super.visit(node, _void);
        Ellipses ellipses = node.getEllipses();
        if (ellipses == Ellipses.NONE)
            return node;

        node = node.shallowCopy();
        node.setCellAttributes(new HashMap<String, String>(node.getCellAttributes()));
        node.setEllipses(Ellipses.NONE);

        DataStructureSort dataStructureSort
                = context.dataStructureSortOf(context.getCellSort(node));
        if (dataStructureSort != null) {
            /* data structure sort */
            if (ellipses == Ellipses.BOTH && !dataStructureSort.type().equals(Sort.LIST)) {
                ellipses = Ellipses.RIGHT;
            }

            Term content = node.getContents();
            if (ellipses == Ellipses.BOTH || ellipses == Ellipses.LEFT) {
                content = KApp.of(
                        KLabelConstant.of(dataStructureSort.constructorLabel()),
                        Variable.getAnonVar(dataStructureSort.sort()),
                        content);
            }
            if (ellipses == Ellipses.BOTH || ellipses == Ellipses.RIGHT) {
                content = KApp.of(
                        KLabelConstant.of(dataStructureSort.constructorLabel()),
                        content,
                        Variable.getAnonVar(dataStructureSort.sort()));
            }

            node.setContents(content);
            return node;
        }

        Sort kind = context.getCellSort(node).getKSort().mainSort();
        Collection col;
        if (node.getContents() instanceof Collection) {
            col = (Collection) node.getContents().shallowCopy();
            col.setContents(new ArrayList<Term>(col.getContents()));
        } else {
            col = MetaK.createCollection(node.getContents(), kind);
            if (col == null) {
                throw KExceptionManager.compilerError(
                        "Expecting a collection item here but got " + node.getContents() + " which is of sort " + kind,
                        this, node);

            }
        }
        node.setContents(col);

        if (ellipses == Ellipses.BOTH && !kind.equals(Sort.K)) {
            ellipses = Ellipses.RIGHT;
        }
        if (ellipses == Ellipses.BOTH || ellipses == Ellipses.LEFT) {
            col.getContents().add(0, Variable.getAnonVar(Sort.of(kind.toString())));
        }
        if (ellipses == Ellipses.BOTH || ellipses == Ellipses.RIGHT) {
            col.getContents().add(Variable.getAnonVar(Sort.of(kind.toString())));
        }

        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _void)  {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _void)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _void)  {
        return node;
    }

}

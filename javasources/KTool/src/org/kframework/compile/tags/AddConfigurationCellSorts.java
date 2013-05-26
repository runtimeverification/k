package org.kframework.compile.tags;

import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;


/**
 * Visitor class adding sort information to each cell in the configuration declaration.
 *
 * @author AndreiS
 */
public class AddConfigurationCellSorts extends BasicVisitor {

    public AddConfigurationCellSorts() {
        /* this visitor does not use the context, so it passes null as the context reference */
        super("Add sort information to configuration cells", null);
    }

    @Override
    public void visit(Configuration node) {
        /* only visit the configuration declaration */
        super.visit(node);
    }

    @Override
    public void visit(Cell node) {
        /* set the sort information as an attribute */
        node.getCellAttributes().put(Cell.SORT_ATTRIBUTE, node.getContents().getSort());
        super.visit(node);
    }

    @Override
    public void visit(Context node) { }

    @Override
    public void visit(Rule node) { }

    @Override
    public void visit(Syntax node) { }

}

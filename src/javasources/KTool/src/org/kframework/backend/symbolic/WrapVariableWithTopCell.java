// Copyright (c) 2012-2014 K Team. All Rights Reserved.

package org.kframework.backend.symbolic;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 12/2/13
 * Time: 11:32 AM
 * This class wraps each occurrence of a variable into a term
 * with the K configuration top cell, together with a given
 * path condition.
 */
public class WrapVariableWithTopCell extends CopyOnWriteTransformer {

    private Term pathCondition;
    private String ltlVarStateName;

    public WrapVariableWithTopCell(Context context, Term pathCondition, String ltlVarStateName) {
        super("Concatenate path condition cell to given Bag (variable)", context);
        this.pathCondition = pathCondition;
        this.ltlVarStateName = ltlVarStateName;
    }

    @Override
    public ASTNode visit(Variable node, Void _)  {
        if (node.getName().equals(ltlVarStateName)) {
            return wrapPCAndVarWithGeneratedTop(pathCondition, node);
        }

        return super.visit(node, _);
    }

    /**
     * Wraps a configuration and a path condition with the generatedTop cell.
     * @param pathCondition is the content of the path condition cell
     * @param configuration is a variable of sort Bag
     * @return The term:
     *  <generatedTop> configuration <path-condition> pathCondition </path-condition> </generatedTop>
     */
    public static Term wrapPCAndVarWithGeneratedTop(Term pathCondition, Term configuration) {
        //create the path condition cell
        Cell pathConditionCell = new Cell();
        pathConditionCell.setLabel(MetaK.Constants.pathCondition);
        pathConditionCell.setEllipses(Cell.Ellipses.NONE);
        pathConditionCell.setContents(pathCondition);

        // build the top cell content
        Bag topCellContent = new Bag();
        java.util.List<Term> bagContents = new ArrayList<Term>();
        bagContents.add(configuration.shallowCopy());
        bagContents.add(pathConditionCell.shallowCopy());
        topCellContent.setContents(bagContents);

        // create the top cell and set bag as content
        Cell topCell = new Cell();
        topCell.setLabel(MetaK.Constants.generatedTopCellLabel);
        topCell.setEllipses(Cell.Ellipses.NONE);
        topCell.setContents(topCellContent);

        return topCell;
    }
}

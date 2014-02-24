package org.kframework.backend.java.indexing.pathIndex.util;

import org.kframework.backend.java.indexing.pathIndex.visitors.TermVisitor;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.backend.java.util.LookupCell;
import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.*;

/**
 * Author: OwolabiL
 * Date: 2/4/14
 * Time: 3:34 PM
 */
public class MultipleCellUtil {

    public static MultiplicityStarCellHolder checkDefinitionForMultiplicityStar(Context context) {
        MultiplicityStarCellHolder starCellHolder = null;
        for (Map.Entry<String, ConfigurationStructure> entry : context.getConfigurationStructureMap().entrySet()) {

            //for now I am assuming that there is only one cell in the definition which (1) has
            // multiplicity* and (2) has children which can contain kCells
            if (entry.getValue().multiplicity.equals(org.kframework.kil.Cell.Multiplicity.ANY)) {
                Term backendKILCell;
                try {
                    backendKILCell = (Cell) entry.getValue().cell.accept(new KILtoBackendJavaKILTransformer(context));
                    Term kCell = LookupCell.find(backendKILCell, "k");
                    if (kCell != null && LookupCell.find(kCell, "k") != null) {
                        starCellHolder = new MultiplicityStarCellHolder();
                        starCellHolder.setCellWithMultipleK(entry.getKey());
                        starCellHolder.setParentOfCellWithMultipleK(entry.getValue().parent.cell.getId());
                    }
                } catch (TransformerException e) {
                    e.printStackTrace();
                }
            }
        }

        return starCellHolder;
    }

    /**
     * Finds the multiple k cells in a rule if they exist
     *
     * @param rule              The rule to be checked
     * @param cellWithMultipleK The cell which has a multiplicity star attribute
     * @return the multiple kCells (where they exist)
     */
    public static ArrayList<Cell> checkRuleForMultiplicityStar(Rule rule, String cellWithMultipleK) {
        Term lhs = rule.leftHandSide();
        Cell withMultipleA = LookupCell.find(lhs, cellWithMultipleK);
        Collection<Cell> innerInnerCell = ((CellCollection) withMultipleA.getContent()).cells();
        ArrayList<Cell> kCells = new ArrayList<>();
        if (innerInnerCell.size() > 1) {
            for (Cell innerInner : innerInnerCell) {
                Cell kCell = LookupCell.find(innerInner, "k");
                kCells.add(kCell);
            }
        }

        return kCells;
    }
}

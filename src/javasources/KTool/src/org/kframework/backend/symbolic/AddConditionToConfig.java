// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Configuration;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.Terminal;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

/**
 * Add cell which holds the path condition to the configuration. The path
 * condition cell is added subcell of <generatedTop>.
 *
 * @author andreiarusoaie
 */
public class AddConditionToConfig extends CopyOnWriteTransformer {

    public static String KCELL = "k";
    public static boolean PC = true;
    public static String PC_VAR = "$PC";

    public AddConditionToConfig(Context context) {
        super("Add path condition to configuration", context);
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {

        // create the path condition cell
        Cell cell = new Cell();
        cell.setLabel(MetaK.Constants.pathCondition);
        cell.setEllipses(Ellipses.NONE);
        if (PC) {
            Variable pc = new Variable(PC_VAR, "Bool");
            cell.setContents(pc);
            context.configVarSorts.put(pc.getName(), pc.getSort());
        }
        else 
            cell.setContents(BoolBuiltin.TRUE);
        // append the path condition cell as subcell of generated top cell
        Term body = node.getBody();
        if (body instanceof Cell) {
            // addCellNextToKCell((Cell) body, cell);
            Cell topCell = (Cell) body;
            if (topCell.getLabel()
                    .equals(MetaK.Constants.generatedTopCellLabel)) {
                node = node.shallowCopy();
                node.setBody(addSubcellToCell(topCell, cell));
                return node;
            }
        }

        return node;
    }

    public static Cell addSubcellToCell(Cell pCell, Cell cCell) {
        if (pCell == null || cCell == null)
            return null;

        Term cont = pCell.getContents();
        if (cont instanceof Bag) {
            Bag conts = (Bag) cont;
            List<Term> contents = new ArrayList<Term>();
            contents.addAll(conts.getContents());
            contents.add(cCell);
            pCell = pCell.shallowCopy();
            pCell.setContents(new Bag(contents));
        } else if (cont instanceof Cell) {
            Cell conts = (Cell) cont;
            List<Term> contents = new ArrayList<Term>();
            contents.add(conts);
            contents.add(cCell);
            pCell = pCell.shallowCopy();
            pCell.setContents(new Bag(contents));
        }

        return pCell;
    }

    public static boolean addCellNextToKCell(Cell cell, Cell toAdd) {

        Term contents = cell.getContents();
        if (contents instanceof Bag) {
            Bag content = (Bag) contents;
            List<Term> subCells = content.getContents();
            for (Term subCell : subCells) {
                if (subCell instanceof Cell
                        && ((Cell) subCell).getLabel().equals(KCELL))
                // the cell kcell has been found as subcell of cell
                {
                    subCells.add(toAdd);
                    cell = cell.shallowCopy();
                    cell.setContents(new Bag(subCells));
                    return true;
                }
            }

            // none of the subcells of cell contains a cell labeled kcell
            for (Term subCell : subCells) {
                if (subCell instanceof Cell) {
                    boolean added = addCellNextToKCell((Cell) subCell, toAdd);
                    if (added)
                        return true;
                }
            }
        }
        if (contents instanceof Cell) {
            Cell subCell = (Cell) contents;
            if (subCell.getLabel().equals(KCELL))
            // the cell kcell has been found as subcell of cell
            {
                List<Term> subCells = new ArrayList<Term>();
                subCells.add(subCell);
                subCells.add(toAdd);
                cell = cell.shallowCopy();
                cell.setContents(new Bag(subCells));
                return true;
            }

            // none of the subcells of cell contains a cell labeled kcell
            boolean added = addCellNextToKCell(subCell, toAdd);
            if (added)
                return true;
        }
        return false;
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        ASTNode result = super.visit(node, _);
        if (result == node)
            return node;
        if (result == null) {
            GlobalSettings.kem
                    .register(new KException(
                            ExceptionType.ERROR,
                            KExceptionGroup.COMPILER,
                            "Expecting Module, but got null. Returning the untransformed module.",
                            getName(), node.getFilename(), node.getLocation()));
            return node;
        }
        if (!(result instanceof Module)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.INTERNAL, "Expecting Module, but got "
                    + result.getClass() + " while transforming.", node
                    .getFilename(), node.getLocation()));
            return node;
        }
        node = (Module) result;
        List<PriorityBlock> topCellBlocks = new ArrayList<PriorityBlock>();
        PriorityBlock topPriorityBlock = new PriorityBlock();
        List<ProductionItem> topTerminals = new ArrayList<ProductionItem>();
        topTerminals.add(new Terminal(MetaK.Constants.pathCondition));
        Production topProduction = new Production(new Sort("CellLabel"),
                topTerminals);
        topPriorityBlock.getProductions().add(topProduction);
        topCellBlocks.add(topPriorityBlock);
        Syntax topCellDecl = new Syntax(new Sort("CellLabel"), topCellBlocks);
        node.getItems().add(topCellDecl);
        return node;
    }

}

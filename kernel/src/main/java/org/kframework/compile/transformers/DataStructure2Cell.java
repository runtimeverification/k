// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.CellMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.CellDataStructure;
import org.kframework.kil.CellList;
import org.kframework.kil.Configuration;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.List;
import java.util.function.Consumer;

import com.google.common.collect.Lists;


/**
 * Translates a builtin data structure (list, map, set)
 * from a {@link org.kframework.kil.DataStructureBuiltin} representation
 * to a {@link org.kframework.kil.Cell} representation.
 * Inverse transformation of {@link Cell2DataStructure}.
 *
 * Does not support functions on cells.
 *
 * @author AndreiS
 */
public class DataStructure2Cell extends CopyOnWriteTransformer {

    public DataStructure2Cell(Context context) {
        super("Transform cells with key attribute to maps", context);
    }

    @Override
    public ASTNode visit(Cell cell, Void _void)  {
        cell = (Cell) super.visit(cell, _void);

        CellDataStructure cellDataStructure = context.cellDataStructures.get(cell.getLabel());
        if (cellDataStructure == null) {
            return cell;
        }

        Bag content;
        if (cellDataStructure instanceof CellList) {
            content = getListCells((ListBuiltin) cell.getContents());
        } else if (cellDataStructure instanceof CellMap) {
            content = getMapCells((MapBuiltin) cell.getContents(), (CellMap) cellDataStructure);
        } else {
            assert false;
            return null;
        }

        Cell returnCell = cell.shallowCopy();
        returnCell.setContents(content);
        return returnCell;
    }

    private Bag getListCells(ListBuiltin listBuiltin) {
        List<Term> cells = Lists.newArrayList();
        Consumer<Term> action = element -> cells.add(getNonLegacyTerm(element));
        listBuiltin.elementsLeft().stream().forEach(action);
        cells.addAll(listBuiltin.baseTerms());
        listBuiltin.elementsRight().stream().forEach(action);

        return new Bag(cells);
    }

    private Bag getMapCells(MapBuiltin mapBuiltin, CellMap cellMap) {
        List<Term> cells = Lists.newArrayList();
        mapBuiltin.elements().entrySet().stream().forEach(entry ->
                cells.add(new Cell(
                        cellMap.entryCellLabel(),
                        new Bag(Lists.<Term>newArrayList(
                                new Cell(cellMap.keyCellLabel(), entry.getKey()),
                                ((Cell) getNonLegacyTerm(entry.getValue())).getContents())))));
        cells.addAll(mapBuiltin.baseTerms());

        return new Bag(cells);
    }

    private Term getNonLegacyTerm(Term term) {
        if (context.kompileOptions.experimental.legacyKast) {
            return ((KInjectedLabel) ((KApp) term).getLabel()).getTerm();
        } else {
            return term;
        }
    }

    @Override
    public ASTNode visit(Configuration configuration, Void _void) {
        return configuration;
    }

}


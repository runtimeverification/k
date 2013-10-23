package org.kframework.compile.transformers;

import org.kframework.compile.utils.CellMap;
import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * Translates a map from a {@link Cell} representation to a {@link MapBuiltin} representation.
 *
 * Does not support functions on cells.
 *
 * @author AndreiS
 */
public class Cell2Map extends CopyOnWriteTransformer {

    public static final String KEY_CELL_ATTRIBUTE_NAME = "key";

    public Cell2Map(Context context) {
        super("Transform cells with key attribute to maps", context);
    }

    @Override
    public ASTNode transform(Configuration configuration) {
        return configuration;
    }

    @Override
    public ASTNode transform(Cell cell) throws TransformerException {
        // TODO(AndreiS): should only be applied once
        makeCellMaps();

        CellMap cellMap = context.cellMaps.get(cell.getLabel());
        DataStructureSort mapSort = context.dataStructureSortOf(DataStructureSort.DEFAULT_MAP_SORT);
        if (cellMap == null) {
            return super.transform(cell);
        }

        Bag cellContent = null;
        if (cell.getContents() instanceof Bag) {
            cellContent = Bag.flatten((Bag) cell.getContents());
        } else if (cell.getContents() instanceof Cell || cell.getContents() instanceof Variable) {
            cellContent = new Bag(Collections.singletonList(cell.getContents()));
        } else {
            assert false;
        }

        Map<Term, Term> entries = new HashMap<>();
        Collection<Term> terms = new ArrayList<>();
        for (Term term : cellContent.getContents()) {
            if (term instanceof Cell) {
                Cell entryCell = (Cell) term;
                assert entryCell.getLabel().equals(cellMap.entryCellLabel());

                Bag entryCellContent = null;
                if (entryCell.getContents() instanceof Bag) {
                    entryCellContent = (Bag) entryCell.getContents();
                } else if (entryCell.getContents() instanceof Cell
                           || entryCell.getContents() instanceof Variable) {
                    entryCellContent = new Bag(Collections.singletonList(entryCell.getContents()));
                } else {
                    assert false;
                }

                Term key = null;
                Bag value = new Bag();
                for (Term term1 : entryCellContent.getContents()) {
                    if (term1 instanceof Cell
                        && ((Cell) term1).getLabel().equals(cellMap.keyCellLabel())) {
                        assert key == null : "there should be exactly one key cell";
                        key = ((Cell) term1).getContents();
                    } else {
                        value.getContents().add(term1);
                    }
                }

                assert key != null : "there should be exactly one key cell";
                // TODO(AndreiS): allow for maps from K to Cells
                // entries.put(key, value);
                assert value.getContents().size() == 1 : "value have sort K";
                entries.put(key, ((Cell) value.getContents().get(0)).getContents());
            } else if (term instanceof Variable) {
                terms.add(new Variable(((Variable) term).getName(), mapSort.name()));
            } else {
                assert false;
            }
        }

        Cell returnCell = cell.shallowCopy();
        returnCell.setContents(new MapBuiltin(mapSort, entries, terms));
        return returnCell;
    }

    private void makeCellMaps() {
        for (ConfigurationStructure cell : context.getConfigurationStructureMap().values()) {
            makeCellMap(cell);
        }
    }

    private void makeCellMap(ConfigurationStructure keyConfigurationStructure) {
        if (!keyConfigurationStructure.cell.containsCellAttribute(KEY_CELL_ATTRIBUTE_NAME)) {
            return;
        }
        String keyCellLabel = keyConfigurationStructure.id;

        ConfigurationStructure entryConfigurationStructure = keyConfigurationStructure.parent;
        if (entryConfigurationStructure.multiplicity != Cell.Multiplicity.ANY) {
            assert false;
            return;
        }
        String entryCellLabel = entryConfigurationStructure.id;

        ConfigurationStructure mapConfigurationStructure = entryConfigurationStructure.parent;
        if (mapConfigurationStructure.sons.size() != 1) {
            assert false;
            return;
        }
        String mapCellLabel = mapConfigurationStructure.id;

        context.cellMaps.put(
                mapCellLabel,
                new CellMap(mapCellLabel, entryCellLabel, keyCellLabel));
    }



}

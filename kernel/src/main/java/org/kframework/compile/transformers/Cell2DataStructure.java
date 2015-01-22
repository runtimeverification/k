// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.CellMap;
import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.CellDataStructure;
import org.kframework.kil.CellList;
import org.kframework.kil.Configuration;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KItemProjection;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Translates a builtin data structure (list, map, set) from a {@link Cell} representation
 * to a {@link DataStructureBuiltin} representation.
 * Inverse transformation of {@link DataStructure2Cell}.
 *
 * Does not support functions on cells.
 *
 * @author AndreiS
 */
public class Cell2DataStructure extends CopyOnWriteTransformer {

    public static final String LIST_CELL_ATTRIBUTE_NAME = "list";
    public static final String MAP_CELL_ATTRIBUTE_NAME = "map";
    public static final String KEY_CELL_ATTRIBUTE_NAME = "key";

    public static final String MAP_CELL_CELL_LABEL_PREFIX = "value-cell-label-prefix-";

    private boolean madeCellDataStructures = false;

    public Cell2DataStructure(Context context) {
        super("Transform cells with key attribute to maps", context);
    }

    @Override
    public ASTNode visit(Configuration configuration, Void _void) {
        return configuration;
    }

    @Override
    public ASTNode visit(Cell cell, Void _void)  {
        if (!madeCellDataStructures) {
            makeCellDataStructures(context);
            madeCellDataStructures = true;
        }

        cell = (Cell) super.visit(cell, _void);

        CellDataStructure cellDataStructure = context.cellDataStructures.get(cell.getLabel());
        if (cellDataStructure == null) {
            return cell;
        }

        Bag cellContent = normalizeCellContent(cell.getContents());

        DataStructureBuiltin dataStructureBuiltin;
        if (cellDataStructure instanceof CellList) {
            dataStructureBuiltin = getListBuiltin(cellContent, (CellList) cellDataStructure, context);
        } else if (cellDataStructure instanceof CellMap) {
            dataStructureBuiltin = getMapBuiltin(cellContent, (CellMap) cellDataStructure, context);
        } else {
            assert false;
            return null;
        }

        Cell returnCell = cell.shallowCopy();
        returnCell.setContents(dataStructureBuiltin);
        return returnCell;
    }

    public static Bag normalizeCellContent(Term content) {
        if (content instanceof Bag) {
            return Bag.flatten((Bag) content);
        } else if (content instanceof Cell
                || content instanceof DataStructureBuiltin
                || content instanceof Variable
                || content instanceof KItemProjection) {
            return new Bag(Collections.singletonList(content));
        } else {
            assert false;
            return null;
        }
    }

    public static ListBuiltin getListBuiltin(Bag cellContent, CellList cellList, Context context) {
        DataStructureSort listSort = context.dataStructureSortOf(
                DataStructureSort.DEFAULT_LIST_SORT);

        List<Term> cellItems = cellContent.getContents();

        int leftIndex;
        List<Term> elementsLeft = new ArrayList<>();
        for (leftIndex = 0; leftIndex < cellItems.size(); ++leftIndex) {
            Term term = cellItems.get(leftIndex);
            if (!(term instanceof Cell)) {
                break;
            }
            Cell elementCell = (Cell) term;
            assert elementCell.getLabel().equals(cellList.elementCellLabel());
            if (!context.kompileOptions.experimental.legacyKast) {
                elementsLeft.add(elementCell);
            } else {
                elementsLeft.add(KApp.of(new KInjectedLabel(elementCell)));
            }
        }

        int rightIndex;
        List<Term> elementsRight = new ArrayList<>();
        for (rightIndex = cellItems.size() - 1; rightIndex >= leftIndex; --rightIndex) {
            Term term = cellItems.get(rightIndex);
            if (!(term instanceof Cell)) {
                break;
            }
            Cell elementCell = (Cell) term;
            assert elementCell.getLabel().equals(cellList.elementCellLabel());
            if (!context.kompileOptions.experimental.legacyKast) {
                elementsRight.add(elementCell);
            } else {
                elementsRight.add(KApp.of(new KInjectedLabel(elementCell)));
            }
        }

        List<Term> terms = new ArrayList<>();
        for (int index = leftIndex; index <= rightIndex; ++index) {
            Term term = cellItems.get(index);
            if (term instanceof Cell) {
                terms.add(term);
            } else if (term instanceof Variable) {
                terms.add(new Variable(((Variable) term).getName(), Sort.of(listSort.name())));
            } else {
                assert false;
            }
        }

        return ListBuiltin.of(listSort, terms, elementsLeft, elementsRight);
    }

    public static MapBuiltin getMapBuiltin(Bag cellContent, CellMap cellMap, Context context) {
        DataStructureSort mapSort = context.dataStructureSortOf(
                DataStructureSort.DEFAULT_MAP_SORT);

        Map<Term, Term> entries = new HashMap<>();
        Collection<Term> terms = new ArrayList<>();
        for (Term term : cellContent.getContents()) {
            if (term instanceof Cell) {
                Cell entryCell = (Cell) term;
                assert entryCell.getLabel().equals(cellMap.entryCellLabel());

                Bag entryCellContent = normalizeCellContent(entryCell.getContents());

                Term key = null;
                Cell value = new Cell();
                value.setLabel(MAP_CELL_CELL_LABEL_PREFIX + entryCell.getLabel());
                value.setEndLabel(MAP_CELL_CELL_LABEL_PREFIX + entryCell.getLabel());
                Bag valueContent = new Bag();
                value.setContents(valueContent);
                for (Term entryCellTerm : entryCellContent.getContents()) {
                    if (entryCellTerm instanceof Cell
                            && ((Cell) entryCellTerm).getLabel().equals(cellMap.keyCellLabel())) {
                        assert key == null : "there should be exactly one key cell";
                        key = ((Cell) entryCellTerm).getContents();
                    } else {
                        valueContent.add(entryCellTerm);
                    }
                }

                assert key != null : "there should be exactly one key cell";
                entries.put(key, value);
                if (!context.kompileOptions.experimental.legacyKast) {
                    entries.put(key, value);
                } else {
                    entries.put(key, KApp.of(new KInjectedLabel(value)));
                }
            } else if (term instanceof MapBuiltin) {
                terms.addAll(((MapBuiltin) term).baseTerms());
                entries.putAll(((MapBuiltin) term).elements());
            } else if (term instanceof Variable) {
                terms.add(new Variable(((Variable) term).getName(), Sort.of(mapSort.name())));
            } else if (term instanceof KItemProjection) {
                terms.add(((KItemProjection) term).getTerm());
            } else {
                assert false;
            }
        }

        return new MapBuiltin(mapSort, terms, entries);
    }

    public static void makeCellDataStructures(Context context) {
        for (ConfigurationStructure cfgStruct : context.getConfigurationStructureMap().values()) {
            makeCellDataStructure(cfgStruct, context);
        }
    }

    private static void makeCellDataStructure(ConfigurationStructure configurationStructure, Context context) {
        if (configurationStructure.cell.containsCellAttribute(LIST_CELL_ATTRIBUTE_NAME)) {
            String listCellLabel = configurationStructure.id;

            if (configurationStructure.sons.size() != 1) {
                assert false;
                return;
            }
            ConfigurationStructure elementConfigurationStructure
                    = configurationStructure.sons.values().iterator().next();

            String elementCellLabel = elementConfigurationStructure.id;

            context.cellDataStructures.put(
                    listCellLabel,
                    new CellList(listCellLabel, elementCellLabel));
        } else if (configurationStructure.cell.containsCellAttribute(MAP_CELL_ATTRIBUTE_NAME)) {
            String mapCellLabel = configurationStructure.id;

            if (configurationStructure.sons.size() != 1) {
                assert false;
                return;
            }
            ConfigurationStructure entryConfigurationStructure
                    = configurationStructure.sons.values().iterator().next();

            String entryCellLabel = entryConfigurationStructure.id;

            ConfigurationStructure keyConfigurationStructure = null;
            for (ConfigurationStructure child : entryConfigurationStructure.sons.values()) {
                if (child.cell.containsCellAttribute(KEY_CELL_ATTRIBUTE_NAME)) {
                    if (keyConfigurationStructure != null) {
                        assert false;
                        return;
                    }
                    keyConfigurationStructure = child;
                }
            }
            if (keyConfigurationStructure == null) {
                assert false;
                return;
            }

            String keyCellLabel = keyConfigurationStructure.id;

            context.cellSorts.put(MAP_CELL_CELL_LABEL_PREFIX + entryCellLabel, Sort.BAG);
            context.cellDataStructures.put(
                    mapCellLabel,
                    new CellMap(mapCellLabel, entryCellLabel, keyCellLabel));
        }
    }

}

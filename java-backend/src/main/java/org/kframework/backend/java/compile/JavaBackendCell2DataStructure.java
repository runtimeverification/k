// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.compile;

import org.kframework.backend.java.kil.JavaBackendRuleData;
import org.kframework.compile.transformers.Cell2DataStructure;
import org.kframework.compile.utils.CellMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.CellDataStructure;
import org.kframework.kil.CellList;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;

import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Java-backend-specific version of {@code Cell2DataStructure} which modifies
 * the {@code JavaBackendRuleData} accordingly and deals with pattern label used
 * by matching logic prover.
 *
 * @see Cell2DataStructure
 */
public class JavaBackendCell2DataStructure extends Cell2DataStructure {

    private Set<String> cellMapLabels = Sets.newHashSet();

    private String patternLabel;

    public JavaBackendCell2DataStructure(Context context) {
        super(context);
    }

    @Override
    public ASTNode visit(Rule rule, Void _) {
        // TODO(AndreiS): should only be applied once
        makeCellDataStructures();
        if ((rule.getBody().getSort().equals(Sort.BAG) || rule.getBody().getSort().equals(Sort.BAG_ITEM))
                && rule.containsAttribute(Attribute.PATTERN_KEY)) {
            patternLabel = ((Cell) ((Rewrite) rule.getBody()).getLeft()).getLabel();
        } else {
            patternLabel = null;
        }

        JavaBackendRuleData ruleData = rule.getAttribute(JavaBackendRuleData.class);
        if (ruleData == null || !ruleData.isCompiledForFastRewriting()) {
            return super.visit(rule, _);
        }

        cellMapLabels.clear();

        rule = (Rule) super.visit(rule, _);
        /* compiling cell to cell map changes the cells of interest used for fast rewriting */
        if (!cellMapLabels.isEmpty()) {
            Set<String> cellsOfInterest = Sets.newHashSet(rule.getAttribute(JavaBackendRuleData.class).getCellsOfInterest());
            Map<String, Term> lhsOfReadCell = Maps.newHashMap(rule.getAttribute(JavaBackendRuleData.class).getLhsOfReadCell());
            Map<String, Term> rhsOfWriteCell = Maps.newHashMap(rule.getAttribute(JavaBackendRuleData.class).getRhsOfWriteCell());
            Set<String> cellMapLabelsToAdd = Sets.newHashSet();

            Iterator<String> iter = cellsOfInterest.iterator();
            while (iter.hasNext()) {
                String cellLabel = iter.next();

                Set<String> intersect = Sets.intersection(
                                context.getConfigurationStructureMap().get(cellLabel).ancestorIds,
                                cellMapLabels);
                /* lift the cell of interest to the level of cell map */
                if (!intersect.isEmpty()) {
                    iter.remove();

                    assert intersect.size() == 1;
                    String cellMapLabel = intersect.iterator().next();
                    cellMapLabelsToAdd.add(cellMapLabel);

                    /* update lhsOfReadCell & rhsOfWriteCell accordingly */
                    if (lhsOfReadCell.containsKey(cellLabel)) {
                        lhsOfReadCell.put(cellMapLabel, null);
                        lhsOfReadCell.remove(cellLabel);
                    }
                    if (rhsOfWriteCell.containsKey(cellLabel)) {
                        rhsOfWriteCell.put(cellMapLabel, null);
                        rhsOfWriteCell.remove(cellLabel);
                    }
                }
            }
            cellsOfInterest.addAll(cellMapLabelsToAdd);

            rule = rule.shallowCopy();
            ruleData = ruleData.setCellsOfInterest(cellsOfInterest);
            ruleData = ruleData.setRhsOfWriteCell(rhsOfWriteCell);
            ruleData = ruleData.setLhsOfReadCell(lhsOfReadCell);
            rule.addAttribute(JavaBackendRuleData.class, ruleData);
        }

        return rule;
    }

    @Override
    public ASTNode visit(Cell cell, Void _)  {
        CellDataStructure cellDataStructure = context.cellDataStructures.get(cell.getLabel());
        if (cellDataStructure == null) {
            return super.visit(cell, _);
        } else if (cellDataStructure instanceof CellMap) {
            cellMapLabels.add(cellDataStructure.dataStructureCellLabel());
        }

        Bag cellContent = normalizeCellContent(cell.getContents());
        if (patternLabel != null && cell.getLabel().equals(patternLabel)) {
            cellContent = new Bag(cellContent.getContents().subList(
                    0,
                    cellContent.getContents().size() - 1));
        }

        DataStructureBuiltin dataStructureBuiltin;
        if (cellDataStructure instanceof CellList) {
            dataStructureBuiltin = getListBuiltin(cellContent, (CellList) cellDataStructure);
        } else if (cellDataStructure instanceof CellMap) {
            dataStructureBuiltin = getMapBuiltin(cellContent, (CellMap) cellDataStructure);
        } else {
            assert false;
            return null;
        }

        if (patternLabel != null && cell.getLabel().equals(patternLabel)) {
            MapBuiltin mapBuiltin = (MapBuiltin) dataStructureBuiltin;
            if (!(mapBuiltin.baseTerms().size() == 1 && mapBuiltin.elements().isEmpty())) {
                return mapBuiltin;
            } else {
                return mapBuiltin.baseTerms().iterator().next();
            }
        }
        Cell returnCell = cell.shallowCopy();
        returnCell.setContents(dataStructureBuiltin);
        return returnCell;
    }

}

// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.compile;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.JavaBackendRuleData;
import org.kframework.compile.utils.ConfigurationStructureVisitor;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import com.google.common.collect.Lists;

/**
 * For each non-function rule, compute all cells that we are interested in
 * during rewriting: <li>Human-written rules: all top level cells that are
 * mentioned in the original definition before any transformation;</li> <li>
 * Auto-generated rules: k cells for heating/cooling rules; and stream cells for
 * I/O rules.</li>
 * <p>
 * Therefore, this pass must be performed before {@link AddTopCellRules} but
 * after {@link AddKCell} & {@link AddStreamCells}.
 *
 * @author YilongL
 *
 */
public class ComputeCellsOfInterest extends CopyOnWriteTransformer {

    private boolean compiledForFastRewriting;
    private Set<String> cellsOfInterest = new HashSet<>();
    private Map<String, Term> readCell2LHS = new HashMap<>();
    private Map<String, Term> writeCell2RHS = new HashMap<>();

    private int nestedCellCount;
    private boolean hasRewrite;
    private boolean topMentionedCellUnderRewrite;

    public ComputeCellsOfInterest(Context context) {
        super("compute information for fast rewriting", context);
    }

    @Override
    public ASTNode visit(Definition node, Void _) {
        ConfigurationStructureVisitor cfgVisitor = new ConfigurationStructureVisitor(context);
        cfgVisitor.visitNode(node);
        return super.visit(node, _);
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
    public ASTNode visit(Rule rule, Void _)  {
        rule.addAttribute(JavaBackendRuleData.class, new JavaBackendRuleData());
        if (rule.containsAttribute(Attribute.FUNCTION_KEY)
                || rule.containsAttribute(Attribute.MACRO_KEY)
                || rule.containsAttribute(Attribute.ANYWHERE_KEY)
                || rule.containsAttribute(Attribute.PATTERN_KEY)) {
            rule.addAttribute(JavaBackendRuleData.class, rule.getAttribute(JavaBackendRuleData.class).setCompiledForFastRewriting(false));
            return rule;
        }

        compiledForFastRewriting = true;
        cellsOfInterest.clear();
        readCell2LHS.clear();
        writeCell2RHS.clear();
        nestedCellCount = 0;
        topMentionedCellUnderRewrite = false;
        rule = (Rule) super.visit(rule, _);

        if (compiledForFastRewriting && topMentionedCellUnderRewrite) {
            /**
             * YilongL: Handle the following case where the parent cell of
             * <tasks>, i.e. <T>, is also the parent of <out>:
             * rule (<tasks> .Bag </tasks> => .)
             *      <out>... .List => ListItem("Type checked!\n") </out>
             */
            List<String> cellsToRemove = Lists.newArrayList();
            for (String cellLabel : cellsOfInterest) {
                if (!Collections.disjoint(context.getConfigurationStructureMap().get(cellLabel).ancestorIds, cellsOfInterest)) {
                    cellsToRemove.add(cellLabel);
                    readCell2LHS.remove(cellLabel);
                    writeCell2RHS.remove(cellLabel);
                }
            }
            cellsOfInterest.removeAll(cellsToRemove);
        }

        rule = rule.shallowCopy();
        JavaBackendRuleData ruleData = rule.getAttribute(JavaBackendRuleData.class);
        ruleData = ruleData.setCompiledForFastRewriting(compiledForFastRewriting);
        if (compiledForFastRewriting) {
            ruleData = ruleData.setCellsOfInterest(cellsOfInterest);
            ruleData = ruleData.setLhsOfReadCell(readCell2LHS);
            ruleData = ruleData.setRhsOfWriteCell(writeCell2RHS);
        }
        rule.addAttribute(JavaBackendRuleData.class, ruleData);

        return rule;
    }

    @Override
    public ASTNode visit(Cell cell, Void _)  {
        if (!compiledForFastRewriting) {
            return cell;
        }

        /* TODO(YilongL): cannot handle duplicate cell labels for now */
        String cellLabel = cell.getLabel();
        if (cellsOfInterest.contains(cellLabel)) {
            compiledForFastRewriting = false;
            return cell;
        }

        /* top level cell mentioned in the rule */
        if (nestedCellCount == 0) {
            cellsOfInterest.add(cellLabel);
            readCell2LHS.put(cellLabel, null);
            hasRewrite = false;
        }

        nestedCellCount++;
        cell = (Cell) super.visit(cell, _);
        nestedCellCount--;

        if (nestedCellCount == 0 && hasRewrite) {
            writeCell2RHS.put(cellLabel, null);
        }

        return cell;
    }

    @Override
    public ASTNode visit(Rewrite node, Void _)  {
        if (nestedCellCount == 0) {
            topMentionedCellUnderRewrite = true;

            /* YilongL: handle the case where the top mentioned cell is inside a
             * rewrite, e.g.:
             *   rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .)
             *         <busy> Busy => Busy -Set keys(H) </busy>
             *         <terminated>... .Set => SetItem(T) ...</terminated>
             */
            Cell cell = null;
            if (node.getLeft() instanceof Cell) {
                cell = (Cell) node.getLeft();
            } else if (node.getRight() instanceof Cell) {
                cell = (Cell) node.getRight();
            } else if (node.getLeft() instanceof Bag) {
                Bag bag = (Bag) node.getLeft();
                if (!bag.isEmpty()) {
                    cell = (Cell) bag.getContents().get(0);
                }
            } else {
                Bag bag = (Bag) node.getRight();
                if (!bag.isEmpty()) {
                    cell = (Cell) bag.getContents().get(0);
                }
            }

            assert cell != null : "could not determine cell under rewrite";
            String parentCellLabel = context.getConfigurationStructureMap().get(cell).parent.id;
            if (parentCellLabel.equals(MetaK.Constants.generatedCfgAbsTopCellLabel)) {
                compiledForFastRewriting = false;
            } else {
                cellsOfInterest.add(parentCellLabel);
                readCell2LHS.put(parentCellLabel, null);
                writeCell2RHS.put(parentCellLabel, null);
            }

            return node;
        }

        hasRewrite = true;
        return node;
    }
}

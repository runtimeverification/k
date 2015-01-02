// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.compile;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.JavaBackendRuleData;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.rewritemachine.MatchingInstruction;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.KApp;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Generates {@link Instruction}s of rewrite rules to be executed by the
 * {@link KAbstractRewriteMachine}.
 *
 * @author YilongL
 *
 */
public class GenerateKRewriteMachineInstructions extends CopyOnWriteTransformer {

    private enum Status { CONFIGURATION, RULE }

    private Status status;
    private List<MatchingInstruction> schedule = new ArrayList<>();
    private Set<String> cellsToVisit = new HashSet<>();
    private Deque<String> cellStack = new ArrayDeque<>();
    private Map<String, Set<String>> containingCells = new HashMap<>();

    public GenerateKRewriteMachineInstructions(Context context) {
        super("Generate K rewrite machine instructions", context);
    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
        List<ModuleItem> moduleItems = node.getItems();
        List<ModuleItem> newModuleItems = new ArrayList<>();

        Configuration cfg = null;
        for (ModuleItem item : moduleItems) {
            if (item instanceof Configuration) {
                cfg = (Configuration) item;
                break;
            }
        }

        status = Status.CONFIGURATION;
        cfg = (Configuration) this.visitNode(cfg);

        status = Status.RULE;
        for (ModuleItem item : moduleItems) {
            if (item instanceof Configuration) {
                newModuleItems.add(cfg);
            } else if (item instanceof Rule) {
                newModuleItems.add((ModuleItem) this.visitNode(item));
            } else {
                newModuleItems.add(item);
            }
        }

        node = node.shallowCopy();
        node.setItems(newModuleItems);
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _void)  {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _void)  {
        return node;
    }

    @Override
    public ASTNode visit(Rule rule, Void _void)  {
        if (!rule.getAttribute(JavaBackendRuleData.class).isCompiledForFastRewriting()) {
            return rule;
        }

        /* only visit cells of interest and their ancestors */
        cellsToVisit.clear();
        for (String cellLabel : containingCells.keySet()) {
            if (!Collections.disjoint(containingCells.get(cellLabel), rule.getAttribute(JavaBackendRuleData.class).getCellsOfInterest())) {
                cellsToVisit.add(cellLabel);
            }
        }

        schedule.clear();
        // do not care about the return node; there will be no transformation
        this.visitNode(((Rewrite) rule.getBody()).getLeft());

        rule = rule.shallowCopy();
        rule.addAttribute(JavaBackendRuleData.class, rule.getAttribute(JavaBackendRuleData.class).setInstructions(schedule));

//        System.out.println(rule);
//        System.out.println(rule.getCellsOfInterest());
//        System.out.println(rule.getLhsOfReadCell());
//        System.out.println(rule.getRhsOfWriteCell());
//        System.out.println(rule.getRewritingSchedule());

        return rule;
    }

    @Override
    public ASTNode visit(KApp kApp, Void _void) {
        /* YilongL: this prevents collecting cells injected inside KItems */
        return kApp;
    }

    @Override
    public ASTNode visit(Cell cell, Void _void)  {
        String cellLabelName = cell.getLabel();
        if (status == Status.CONFIGURATION) {
            /* compute childrenCells */

            // TODO(YilongL): perhaps move the following computation to {@link
            // InitializeConfigurationStructure}
            for (String ancestor : cellStack) {
                containingCells.get(ancestor).add(cellLabelName);
            }

            assert !containingCells.containsKey(cellLabelName);
            containingCells.put(cellLabelName, new HashSet<String>());
            containingCells.get(cellLabelName).add(cellLabelName);

            cellStack.push(cellLabelName);
            cell = (Cell) super.visit(cell, _void);
            cellStack.pop();
            return cell;
        } else if (status == Status.RULE) {
            if (!cellsToVisit.contains(cellLabelName)) {
                return cell;
            }

            if (context.getConfigurationStructureMap().get(cellLabelName).isStarOrPlus()) {
                schedule.add(MatchingInstruction.CHOICE);
            }

            schedule.add(MatchingInstruction.GOTO(CellLabel.of(cellLabelName)));
            cell = (Cell) super.visit(cell, _void);
            schedule.add(MatchingInstruction.UP);

            return cell;
        } else {
            assert false;
            return cell; // never reach
        }
    }
}

// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.rewritemachine.Instruction;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
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
    private List<Instruction> schedule = new ArrayList<>();
    private Set<String> cellsToVisit = new HashSet<>();
    private Deque<String> cellStack = new ArrayDeque<>();
    private Map<String, Set<String>> containingCells = new HashMap<>();

    public GenerateKRewriteMachineInstructions(Context context) {
        super("Generate K rewrite machine instructions", context);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
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
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Rule rule, Void _)  {
        if (!rule.isCompiledForFastRewriting()) {
            return rule;
        }

        /* only visit cells of interest and their ancestors */
        cellsToVisit.clear();
        for (String cellLabel : containingCells.keySet()) {
            if (!Collections.disjoint(containingCells.get(cellLabel), rule.getCellsOfInterest())) {
                cellsToVisit.add(cellLabel);
            }
        }

        schedule.clear();
        // do not care about the return node; there will be no transformation
        this.visitNode(((Rewrite) rule.getBody()).getLeft());

        rule = rule.shallowCopy();
        rule.setInstructions(schedule);

//        System.out.println(rule);
//        System.out.println(rule.getCellsOfInterest());
//        System.out.println(rule.getLhsOfReadCell());
//        System.out.println(rule.getRhsOfWriteCell());
//        System.out.println(rule.getRewritingSchedule());

        return rule;
    }

    @Override
    public ASTNode visit(Cell cell, Void _)  {
        String cellLabel = cell.getLabel();
        if (status == Status.CONFIGURATION) {
            /* compute childrenCells */

            // TODO(YilongL): perhaps move the following computation to {@link
            // InitializeConfigurationStructure}
            for (String ancestor : cellStack) {
                containingCells.get(ancestor).add(cellLabel);
            }

            assert !containingCells.containsKey(cellLabel);
            containingCells.put(cellLabel, new HashSet<String>());
            containingCells.get(cellLabel).add(cellLabel);

            cellStack.push(cellLabel);
            cell = (Cell) super.visit(cell, _);
            cellStack.pop();
            return cell;
        } else if (status == Status.RULE) {
            if (!cellsToVisit.contains(cellLabel)) {
                return cell;
            }

            if (context.getConfigurationStructureMap().get(cellLabel).isStarOrPlus()) {
                schedule.add(Instruction.CHOICE);
            }

            schedule.add(Instruction.GOTO(cellLabel));
            cell = (Cell) super.visit(cell, _);
            schedule.add(Instruction.UP);

            return cell;
        } else {
            assert false;
            return cell; // never reach
        }
    }
}

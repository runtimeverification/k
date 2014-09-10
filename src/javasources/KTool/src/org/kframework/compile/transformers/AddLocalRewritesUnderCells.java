// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.kframework.backend.java.kil.JavaBackendRuleData;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

/**
 * Adds local rewrites under the cells of interest computed in
 * {@link ComputeCellsOfInterest} pass. Local rewrites are rewrite operations
 * that are not pushed to the top but just under the cells instead. For example,
 * consider the following rule:
 *
 * <pre>
 * {@code
 * rule <k> X:Id => I:Int ...</k>
 *      <env>... X |-> L ...</env>
 *      <store>... L |-> I ...</store>}
 * </pre>
 *
 * The local rewrite of the k cell would be `X:Id ~> K:K => V:Int ~> K:K', where
 * the original rewrite operation is pushed just one level up to under the k cell.
 * <p>
 * This pass needs to be placed after the last pass that transforms the rewrite
 * rule.
 *
 * @author YilongL
 *
 */
public class AddLocalRewritesUnderCells extends CopyOnWriteTransformer {

    private enum Status { LHS, RHS }

    private Rule crntRule;
    private boolean hasAssocCommMatching;
    private String outerWriteCell = null;
    private Status status;

    private Map<String, Term> lhsOfReadCell;
    private Map<String, Term> rhsOfWriteCell;
    private Set<String> cellsToCopy = Sets.newHashSet();

    public AddLocalRewritesUnderCells(Context context) {
        super("Add local rewrites under cells of interest", context);
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

    private Rule setCellsToCopyForUncompiledRule(Rule rule) {
        JavaBackendRuleData ruleData = rule.getAttribute(JavaBackendRuleData.class);
        if (((Rewrite) rule.getBody()).getRight() instanceof Cell) {
            Cell rhs =  (Cell) ((Rewrite) rule.getBody()).getRight();
            rule = rule.shallowCopy();
            if (hasGroundCell(rhs)) {
                ruleData = ruleData.setCellsToCopy(ImmutableSet.of(rhs.getLabel()));
            } else {
                ruleData = ruleData.setCellsToCopy(ImmutableSet.<String>of());
            }
        } else {
            ruleData = ruleData.setCellsToCopy(ImmutableSet.<String>of());
        }
        rule.addAttribute(JavaBackendRuleData.class, ruleData);
        return rule;
    }

    @Override
    public ASTNode visit(Rule rule, Void _)  {
        if (!rule.getAttribute(JavaBackendRuleData.class).isCompiledForFastRewriting()) {
            return setCellsToCopyForUncompiledRule(rule);
        }

        hasAssocCommMatching = false;
        lhsOfReadCell = Maps.newHashMap(rule.getAttribute(JavaBackendRuleData.class).getLhsOfReadCell());
        rhsOfWriteCell = Maps.newHashMap(rule.getAttribute(JavaBackendRuleData.class).getRhsOfWriteCell());
        cellsToCopy.clear();

        crntRule = rule;
        status = Status.LHS;
        this.visitNode(((Rewrite) rule.getBody()).getLeft());
        if (hasAssocCommMatching) {
            rule = rule.shallowCopy();
            rule.addAttribute(JavaBackendRuleData.class, rule.getAttribute(JavaBackendRuleData.class).setCompiledForFastRewriting(false));
            rule = setCellsToCopyForUncompiledRule(rule);
            return rule;
        }

        status = Status.RHS;
        this.visitNode(((Rewrite) rule.getBody()).getRight());
        status = null;
        crntRule = null;

        rule = rule.shallowCopy();
        JavaBackendRuleData ruleData = rule.getAttribute(JavaBackendRuleData.class);
        ruleData = ruleData.setLhsOfReadCell(lhsOfReadCell);
        ruleData = ruleData.setRhsOfWriteCell(rhsOfWriteCell);
        ruleData = ruleData.setCellsToCopy(cellsToCopy);
        rule.addAttribute(JavaBackendRuleData.class, ruleData);

        return rule;
    }

    @Override
    public ASTNode visit(Cell cell, Void _)  {
        if (crntRule == null) {
            return super.visit(cell, _);
        }
        if (!crntRule.getAttribute(JavaBackendRuleData.class).getCellsOfInterest().contains(cell.getLabel())
                && outerWriteCell == null) {
            return super.visit(cell, _);
        }

        if (status == Status.LHS) {
            if (crntRule.getAttribute(JavaBackendRuleData.class).getReadCells().contains(cell.getLabel())) {
                if (hasAssocCommMatching(cell)) {
                    hasAssocCommMatching = true;
                }
                lhsOfReadCell.put(cell.getLabel(), cell.getContents());
            }
        } else {
            if (outerWriteCell != null) {
                if (isGroundCell(cell)) {
                    cellsToCopy.add(outerWriteCell);
                } else {
                    super.visit(cell, _);
                }
            } else {
                if (crntRule.getAttribute(JavaBackendRuleData.class).getWriteCells().contains(cell.getLabel())) {
                    rhsOfWriteCell.put(cell.getLabel(), cell.getContents());

                    outerWriteCell = cell.getLabel();
                    super.visit(cell, _);
                    outerWriteCell = null;
                }
            }
        }

        return cell;
    }

    private boolean hasAssocCommMatching(Cell cell) {
        final MutableBoolean hasACMatching = new MutableBoolean(false);
        new BasicVisitor(context) {

            @Override
            public Void visit(Cell cell, Void _) {
                if (hasACMatching.booleanValue()) {
                    return null;
                }
                super.visit(cell, _);

                if (!hasACMatching.booleanValue()) {
                    for (Term term : cell.getCellTerms()) {
                        if (term instanceof Cell) {
                            if (context.getConfigurationStructureMap().get((Cell) term).isStarOrPlus()) {
                                hasACMatching.setValue(true);
                                break;
                            }
                        }
                    }
                }

                return null;
            }
        }.visitNode(cell);
        return hasACMatching.booleanValue();
    }

    private boolean hasGroundCell(Cell outerCell) {
        final MutableBoolean hasGroundCell = new MutableBoolean(false);
        new BasicVisitor(context) {

            Set<Cell> visitedCells = Collections.newSetFromMap(new IdentityHashMap<Cell, Boolean>());

            @Override
            public Void visit(Cell cell, Void _) {
                if (hasGroundCell.booleanValue()) {
                    return null;
                }
                if (visitedCells.contains(cell)) {
                    // this cell has been visited before and obviously it's not
                    // a ground cell; otherwise, hasGroundCell must have been
                    // set to true and the traversal is terminated
                    return null;
                }
                super.visit(cell, _);

                visitedCells.add(cell);
                if (!hasGroundCell.booleanValue()) {
                    hasGroundCell.setValue(isGroundCell(cell));
                }
                return null;
            }
        }.visitNode(outerCell);
        return hasGroundCell.booleanValue();
    }

    private boolean isGroundCell(Cell cell) {
        return cell.variables().isEmpty();
    }

}

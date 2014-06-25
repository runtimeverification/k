package org.kframework.compile.transformers;

import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

public class AddLocalRewriteForCellsOfInterest extends CopyOnWriteTransformer {
    
    private enum Status { LHS, RHS }

    private Rule crntRule;
    private String outerWriteCell = null;
    private Status status;
    
    private Map<String, Term> lhsOfReadCell;
    private Map<String, Term> rhsOfWriteCell;  
    private Set<String> cellsToCopy = Sets.newHashSet();

    public AddLocalRewriteForCellsOfInterest(Context context) {
        super("Add local rewrite for cells of interest", context);
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
        if (!rule.isCompiledForFastRewriting()) {
            return rule;
        }
                
        lhsOfReadCell = Maps.newHashMap(rule.getLhsOfReadCell());
        rhsOfWriteCell = Maps.newHashMap(rule.getRhsOfWriteCell());
        cellsToCopy.clear();
        
        crntRule = rule;
        status = Status.LHS;
        this.visitNode(((Rewrite) rule.getBody()).getLeft());
        status = Status.RHS;
        this.visitNode(((Rewrite) rule.getBody()).getRight());
        status = null;
        crntRule = null;
        
        rule = rule.shallowCopy();
        rule.setLhsOfReadCell(lhsOfReadCell);
        rule.setRhsOfWriteCell(rhsOfWriteCell);
        rule.setCellsToCopy(cellsToCopy);
        
        return rule;
    }
    
    @Override
    public ASTNode visit(Cell cell, Void _)  {
        if (crntRule == null) {
            return super.visit(cell, _);
        }
        if (!crntRule.getCellsOfInterest().contains(cell.getLabel()) 
                && outerWriteCell == null) {
            return super.visit(cell, _);
        }

        if (status == Status.LHS) {
            if (crntRule.getReadCells().contains(cell.getLabel())) {
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
                if (crntRule.getWriteCells().contains(cell.getLabel())) {
                    rhsOfWriteCell.put(cell.getLabel(), cell.getContents());
                    
                    outerWriteCell = cell.getLabel();
                    super.visit(cell, _);
                    outerWriteCell = null;
                }                
            }
        }        

        return cell;
    }

    private boolean isGroundCell(Cell cell) {
        final MutableBoolean isGround = new MutableBoolean(true);
        BasicVisitor variableCollector = new BasicVisitor(context) {
            @Override
            public Void visit(Variable variable, Void _) {
                isGround.setValue(false);
                return null;
            }
        };
        variableCollector.visitNode(cell);
        
        return isGround.getValue();
    }
}

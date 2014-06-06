package org.kframework.compile.transformers;

import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import com.google.common.collect.Maps;

public class AddLocalRewriteForCellsOfInterest extends CopyOnWriteTransformer {
    
    private enum Status { LHS, RHS }

    private Rule crntRule;
    private Status status;
    
    private Map<String, Term> lhsOfReadCell;
    private Map<String, Term> rhsOfWriteCell;    

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
        
        crntRule = rule;
        status = Status.LHS;
        this.visitNode(((Rewrite) rule.getBody()).getLeft());
        status = Status.RHS;
        this.visitNode(((Rewrite) rule.getBody()).getRight());
        status = null;
        crntRule = null;
        
        rule.setLhsOfReadCell(lhsOfReadCell);
        rule.setRhsOfWriteCell(rhsOfWriteCell);
        
//        System.out.println(rule);
//        System.out.println(cell2Lhs);
//        System.out.println(cell2Rhs);
//        System.out.println("************");
        return rule;
    }
    
    @Override
    public ASTNode visit(Cell cell, Void _)  {
        if (crntRule == null || (crntRule != null && !crntRule.getCellsOfInterest().contains(cell.getLabel()))) {
            return super.visit(cell, _);
        }
        
        if (status == Status.LHS) {
            if (crntRule.getReadCells().contains(cell.getLabel())) {
                lhsOfReadCell.put(cell.getLabel(), cell.getContents());
            }
        } else {
            if (crntRule.getWriteCells().contains(cell.getLabel())) {
                rhsOfWriteCell.put(cell.getLabel(), cell.getContents());
            }
        }        

        return cell;
    }
}

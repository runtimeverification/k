// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

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

    public ComputeCellsOfInterest(Context context) {
        super("compute information for fast rewriting", context);
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
        if (rule.containsAttribute(Attribute.FUNCTION_KEY)
                || rule.containsAttribute(Attribute.MACRO_KEY)) {
            rule.setCompiledForFastRewriting(false);
            return rule;
        }
        
        compiledForFastRewriting = true;
        cellsOfInterest.clear();
        readCell2LHS.clear();
        writeCell2RHS.clear();
        nestedCellCount = 0;
        rule = (Rule) super.visit(rule, _);

        rule = rule.shallowCopy();
        rule.setCompiledForFastRewriting(compiledForFastRewriting);
        if (compiledForFastRewriting) {
            rule.setCellsOfInterest(cellsOfInterest);
            rule.setLhsOfReadCell(readCell2LHS);
            rule.setRhsOfWriteCell(writeCell2RHS);
        }
        
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
            /* TODO(YilongL): unable to handle the case where the top mentioned
             * cell is inside a rewrite, e.g.:
             *   rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .)
             *         <busy> Busy => Busy -Set keys(H) </busy>
             *         <terminated>... .Set => SetItem(T) ...</terminated>
             */
            compiledForFastRewriting = false;
            return node;
        }
        
        hasRewrite = true;
        return node;
    }
}

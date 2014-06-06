package org.kframework.backend.java.symbolic;

import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

/**
 * 
 * @author YilongL
 *
 */
public class KAbstractRewriteMachine {
    
    public static final String INST_UP = "UP";
    public static final String INST_CHOICE = "*";
    public static final String INST_END = "END";
    
    private final Rule rule;
    private final Cell<?> subject;
    private final List<String> instructions;
    private final List<Cell> writeCells = Lists.newArrayList();
    
    private Map<Variable, Term> substitution = Maps.newHashMap();
    
    // program counter
    private int pc = 0;
    private boolean success = true;
    
    private final TermContext context;
    
    private KAbstractRewriteMachine(Rule rule, Cell<?> subject, TermContext context) {
        this.rule = rule;
        this.subject = subject;
        this.instructions = rule.instructions();
        this.context = context;
    }
    
    public static boolean rewrite(Rule rule, Term subject, TermContext context) {
        KAbstractRewriteMachine machine = new KAbstractRewriteMachine(rule, (Cell<?>) subject, context);
        return machine.rewrite();
    }
    
    private boolean rewrite() {
        execute(subject);
        return success;
    }

    private void execute(Cell<?> crntCell) {
        String cellLabel = crntCell.getLabel();
        if (isReadCell(cellLabel)) {
            // do matching
            Map<Variable, Term> subst = PatternMatcher.patternMatch(crntCell, (Term) rule.lhsOfReadCell().get(cellLabel), context);
            if (subst == null) {
                success = false;
            } else {                    
                substitution = PatternMatcher.composeSubstitution(substitution, subst);
                if (substitution == null) {
                    success = false;
                }
            }
            if (!success) {
                return;
            }
        }
        if (isWriteCell(crntCell.getLabel())) {
            writeCells.add(crntCell);
        }
        
        while (true) {
            String nextInstr = getNextInstruction();
            if (nextInstr == null) {
                for (Cell cell : writeCells) {
                    
                }
            }
            
            if (nextInstr.equals(INST_CHOICE)) {
                // TODO(YilongL): ignore choice instruction for now
                nextInstr = getNextInstruction();
            }
            
            if (nextInstr.equals(INST_UP)) {
                return;
            }
            
            // nextInstr == cell label
            String nextCellLabel = nextInstr;
            Iterator<Cell> cellIter = ((CellCollection) crntCell.getContent()).cellMap().get(nextCellLabel).iterator();
            Cell<?> nextCell = cellIter.next();
            execute(nextCell);
            if (!success) {
                return;
            }
        }
    }

    private String getNextInstruction() {
        return instructions.get(pc++);
    }

    private boolean isReadCell(String cellLabel) {
        return rule.lhsOfReadCell().keySet().contains(cellLabel);
    }

    private boolean isWriteCell(String cellLabel) {
        return rule.rhsOfWriteCell().keySet().contains(cellLabel);
    }
}

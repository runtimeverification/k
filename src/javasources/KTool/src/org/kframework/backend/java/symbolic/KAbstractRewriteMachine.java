package org.kframework.backend.java.symbolic;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.Profiler;

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
    private Collection<Collection<Map<Variable, Term>>> multiSubstitutions = Lists.newArrayList();
    
    // program counter
    private int pc = 1;
    private boolean success = true;
    private boolean isStarNested = false;
    
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
        if (success) {
            Profiler.startTimer(Profiler.EVALUATE_SIDE_CONDITIONS_TIMER);
            List<Map<Variable, Term>> solutions = PatternMatcher.evaluateConditions(rule,
                        PatternMatcher.getMultiSubstitutions(substitution, multiSubstitutions), context);
            Profiler.stopTimer(Profiler.EVALUATE_SIDE_CONDITIONS_TIMER);
            
            if (!solutions.isEmpty()) {
                Map<Variable, Term> solution = solutions.get(0);

                Profiler.startTimer(Profiler.LOCAL_REWRITE_BUILD_RHS_TIMER);
                // YilongL: cannot use solution.keySet() as variablesToReuse
                // because read-only cell may have already used up the binding
                // term
                Transformer substAndEvalTransformer = new CopyOnShareSubstAndEvalTransformer(
                        solution, rule.reusableLhsVariables().elementSet(),
                        context);
                
                for (Cell<Term> cell : writeCells) {
                    Term writeCellPattern = rule.rhsOfWriteCell().get(cell.getLabel());
                    if (rule.cellsToCopy().contains(cell.getLabel())) {
                        writeCellPattern = DeepCloner.clone(writeCellPattern);
                    }
                    Term newContent = (Term) writeCellPattern.accept(substAndEvalTransformer);
                    cell.unsafeSetContent(newContent);
                }
                Profiler.stopTimer(Profiler.LOCAL_REWRITE_BUILD_RHS_TIMER);
            } else {
                success = false;
            }
        }
        
        return success;
    }
    
    private void execute(Cell<?> crntCell) {
        String cellLabel = crntCell.getLabel();
        if (isReadCell(cellLabel)) {
            // do matching
            Profiler.startTimer(Profiler.PATTERN_MATCH_TIMER);
            Map<Variable, Term> subst = PatternMatcher.nonAssocCommPatternMatch(crntCell.getContent(), (Term) rule.lhsOfReadCell().get(cellLabel), context);         
            if (subst == null) {
                success = false;
            } else {                    
                substitution = PatternMatcher.composeSubstitution(substitution, subst);
                if (substitution == null) {
                    success = false;
                }
            }
            Profiler.stopTimer(Profiler.PATTERN_MATCH_TIMER);
            
            if (!success) {
                return;
            }
        }
        if (isWriteCell(crntCell.getLabel())) {
            writeCells.add(crntCell);
        }
        
        while (true) {
            String nextInstr = getNextInstruction();
           
            if (nextInstr.equals(INST_UP)) {
                return;
            }

            if (nextInstr.equals(INST_CHOICE)) {
                assert !isStarNested : "nested cells with multiplicity='*' not supported";
                isStarNested = true;
                
                Map<Variable, Term> oldSubstitution = substitution;
                substitution = Maps.newHashMap();
                Collection<Map<Variable, Term>> substitutions = Lists.newArrayList();

                nextInstr = getNextInstruction();
                int oldPC = pc;
                int newPC = -1;
                for (Cell cell : ((CellCollection) crntCell.getContent()).cellMap().get(nextInstr)) {
                    assert success;
                    pc = oldPC;
                    execute(cell);
                    if (!success) {
                        // flag success must be true before execute the cell
                        success = true;
                        continue;
                    } else {
                        newPC = pc;
                        substitutions.add(substitution);
                        substitution = Maps.newHashMap();
                    }
                }
                
                isStarNested = false;
                if (substitutions.isEmpty()) {
                    success = false;
                    return;
                } else {
                    pc = newPC;
                    multiSubstitutions.add(substitutions);
                    substitution = oldSubstitution;
                }
            } else {
                // nextInstr == cell label
                Iterator<Cell> cellIter = ((CellCollection) crntCell.getContent()).cellMap().get(nextInstr).iterator();
                Cell<?> nextCell = cellIter.next();
                execute(nextCell);
                if (!success) {
                    return;
                }
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

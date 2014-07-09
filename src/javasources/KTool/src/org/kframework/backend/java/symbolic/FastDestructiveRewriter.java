// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.util.Profiler;
import org.kframework.krun.api.SearchType;

import com.google.common.base.Stopwatch;
import com.google.common.collect.Lists;

public class FastDestructiveRewriter extends AbstractRewriter {
    
    private final boolean ENABLE_DEBUG_MODE = false;
    
    private final Stopwatch stopwatch = new Stopwatch();
    
    public FastDestructiveRewriter(Definition definition, TermContext termContext) {
        super(definition, termContext);
    }

    @Override
    public Term rewrite(Term subject, int bound) {
        stopwatch.start();
        
        /* first break any possible sharing of mutable terms introduced by macro
         * expansion or front-end */
        subject = EliminateUnsafeSharingTransformer.transformTerm(subject, termContext);

        /* Invariant during rewriting: 
         *   no sharing between mutable terms inside the subject
         *  
         * In order to maintain this invariant, we need to make sure 
         * the application of the following rules will not introduce
         * any undesired sharing:
         *   - rules kompiled for fast rewrite
         *   - rules not kompiled for fast rewrite
         *   - function rules
         *   
         * Basically all we need to do is to replace the normal subst&eval
         * transformer with the copy-on-share version and supply it with 
         * the correct reusable variables obtained from the pattern match
         * phase */
        for (step = 0; step != bound; ++step) {
            computeRewriteStep(subject, 1);
            Term result = getTransition(0);
            if (result != null) {
                if (ENABLE_DEBUG_MODE) {
                    UnsafeSharingDetector.visitTerm(result);
                }
                subject = result;
            } else {
                computeRewriteStep(subject, 1);
                break;
            }
        }

        stopwatch.stop();
        System.err.println("[" + step + ", " + stopwatch + "]");
        Profiler.printResult();

        return subject;
    }

    protected final void computeRewriteStep(Term subject, int successorBound) {
        results.clear();
        assert successorBound == 1;

        // Applying a strategy to a list of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
        //        System.out.println(LookupCell.find(constrainedTerm.term(),"k"));
        strategy.reset(getRules(subject));

        while (strategy.hasNext()) {
            ArrayList<Rule> rules = new ArrayList<Rule>(strategy.next());
//            System.out.println("rules.size: "+rules.size());
            for (Rule rule : rules) {
                boolean succeed = false;
                if (rule.isCompiledForFastRewriting()) {
                    /* compute reference results using old algorithm under DEBUG mode */
                    List<Term> referenceResults = null;
                    if (ENABLE_DEBUG_MODE) {
                        referenceResults = Lists.newArrayList();
                        for (Map<Variable, Term> subst : getMatchingResults(subject, rule)) {
                            referenceResults.add(constructNewSubjectTerm(rule, subst));
                        }
                        
                        /* eliminate sharing of mutable terms between subject and reference results */
                        subject = DeepCloner.clone(subject);
                    }
                    
                    Profiler.startTimer(Profiler.REWRITE_WITH_KOMPILED_RULES_TIMER);
                    if (succeed = KAbstractRewriteMachine.rewrite(rule, subject, termContext)) {
                        results.add(subject);
                        
                        /* the result of rewrite machine must be in the reference results */
                        if (ENABLE_DEBUG_MODE) {
                            assert referenceResults.contains(subject);
                        }
                    }
                    Profiler.stopTimer(Profiler.REWRITE_WITH_KOMPILED_RULES_TIMER);
                } else {
                    Profiler.startTimer(Profiler.REWRITE_WITH_UNKOMPILED_RULES_TIMER);
                    for (Map<Variable, Term> subst : getMatchingResults(subject, rule)) {
                        results.add(constructNewSubjectTerm(rule, subst));
                        succeed = true;
                        break;
                    }
                    Profiler.stopTimer(Profiler.REWRITE_WITH_UNKOMPILED_RULES_TIMER);
                }
                
                if (succeed) {
                    return;
                }
            }
            // If we've found matching results from one equivalence class then
            // we are done, as we can't match rules from two equivalence classes
            // in the same step.
            if (results.size() > 0) {
                return;
            }
        }
    }

    protected final Term constructNewSubjectTerm(Rule rule, Map<Variable, Term> substitution) {
        Term rhs = rule.cellsToCopy().contains(((Cell) rule.rightHandSide()).getLabel()) ?
                DeepCloner.clone(rule.rightHandSide()) : 
                rule.rightHandSide();
        return rhs.copyOnShareSubstAndEval(substitution, 
                rule.reusableVariables().elementSet(), termContext);
    }

    @Override
    public List<Map<Variable, Term>> search(Term initialTerm, Term targetTerm,
            List<Rule> rules, Rule pattern, int bound, int depth,
            SearchType searchType) {
        throw new UnsupportedOperationException();
    }

}

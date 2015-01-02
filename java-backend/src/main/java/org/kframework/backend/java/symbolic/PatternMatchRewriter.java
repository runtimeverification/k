// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.indexing.IndexingCellsCollector;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.strategies.TransitionCompositeStrategy;
import org.kframework.backend.java.util.Coverage;
import org.kframework.backend.java.util.Profiler;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.SearchType;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;

import com.google.common.base.Stopwatch;
import com.google.common.collect.Lists;
import com.google.inject.Inject;

public class PatternMatchRewriter {

    private final boolean ENABLE_DEBUG_MODE = false;

    private final Stopwatch stopwatch = Stopwatch.createUnstarted();

    private List<CellCollection.Cell> indexingCells = Lists.newArrayList();

    private final KRunOptions options;
    private final JavaExecutionOptions javaOptions;

    private boolean transition;

    private final TransitionCompositeStrategy strategy;
    private int step;
    private final List<Term> results = new ArrayList<>();
    private RuleIndex ruleIndex;

    @Inject
    public PatternMatchRewriter(
            Definition definition,
            KRunOptions options,
            KompileOptions kompileOptions,
            JavaExecutionOptions javaOptions) {
        this.options = options;
        ruleIndex = definition.getIndex();
        this.strategy = new TransitionCompositeStrategy(kompileOptions.transition);
        this.javaOptions = javaOptions;
    }

    public Term rewrite(Term subject, int bound, TermContext termContext) {
        stopwatch.start();

        /* first break any possible sharing of mutable terms introduced by macro
         * expansion or front-end */
        subject = EliminateUnsafeSharingTransformer.transformTerm(subject, termContext);

        /* compute indexing cells of the subject term for the first time */
        computeIndexingCells(subject, termContext);

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
            computeRewriteStep(subject, 1, termContext);
            Term result = getTransition(0);
            if (result != null) {
                if (ENABLE_DEBUG_MODE) {
                    UnsafeSharingDetector.visitTerm(result);
                }
                subject = result;
            } else {
//                computeRewriteStep(subject, 1);
                break;
            }
        }

        stopwatch.stop();
        if (options.experimental.statistics) {
            System.err.println("[" + step + ", " + stopwatch + "]");
            Profiler.printResult();
        }

        return subject;
    }

    private List<Rule> getRules(List<CellCollection.Cell> indexingCells) {
        Profiler.startTimer(Profiler.QUERY_RULE_INDEXING_TIMER);
        List<Rule> rules = ruleIndex.getRules(indexingCells);
        Profiler.stopTimer(Profiler.QUERY_RULE_INDEXING_TIMER);
        return rules;
    }

    /**
     * Gets the rules that could be applied to a given term according to the
     * rule indexing mechanism.
     *
     * @param term
     *            the given term
     * @return a list of rules that could be applied
     */
    private List<Rule> getRules(Term term) {
        return ruleIndex.getRules(term);
    }

    private final Term getTransition(int n) {
        return n < results.size() ? results.get(n) : null;
    }

    /**
     * Returns a list of substitutions obtained by matching the subject against
     * a rewrite rule.
     * <p>
     * This method is extracted to simplify the profiling script.
     * </p>
     */
    private final List<Map<Variable,Term>> getMatchingResults(Term subject, Rule rule, TermContext termContext) {
        return PatternMatcher.match(subject, rule, termContext);
    }

    private void computeIndexingCells(Term subject, TermContext termContext) {
        indexingCells = IndexingCellsCollector.getIndexingCells(subject, termContext.definition());
    }

    private final void computeSearchRewriteStep(Term subject, int successorBound, TermContext termContext) {
        results.clear();

        if (successorBound == 0) {
            return;
        }

        // Applying a strategy to a list of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
        //        System.out.println(LookupCell.find(constrainedTerm.term(),"k"));
        strategy.reset(getRules(subject));

        while (strategy.hasNext()) {
            transition = strategy.nextIsTransition();
            ArrayList<Rule> rules = new ArrayList<Rule>(strategy.next());
//            System.out.println("rules.size: "+rules.size());
            for (Rule rule : rules) {
                for (Map<Variable, Term> subst : getMatchingResults(subject, rule, termContext)) {
                    results.add(constructNewSearchSubjectTerm(rule, subst, termContext));
                    if (results.size() == successorBound) {
                        return;
                    }
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

    private Term constructNewSearchSubjectTerm(Rule rule, Map<Variable, Term> substitution, TermContext termContext) {
        return rule.rightHandSide().substituteAndEvaluate(substitution, termContext);
    }

    private final void computeRewriteStep(Term subject, int successorBound, TermContext termContext) {
        results.clear();
        assert successorBound == 1;

        RuleAuditing.setAuditingRule(javaOptions, step, termContext.definition());

        File coverage = options.experimental.coverage;
        Coverage.print(coverage, subject);

        // Applying a strategy to a list of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
        strategy.reset(getRules(indexingCells));
        try {

            while (strategy.hasNext()) {
                ArrayList<Rule> rules = new ArrayList<Rule>(strategy.next());
    //            System.out.println("rules.size: "+rules.size());
                for (Rule rule : rules) {
                    try {
                        if (rule == RuleAuditing.getAuditingRule()) {
                            RuleAuditing.beginAudit();
                        } else if (RuleAuditing.isAuditBegun() && RuleAuditing.getAuditingRule() == null) {
                            System.err.println("\nAuditing " + rule + "...\n");
                        }
                        boolean succeed = false;
                        if (rule.isCompiledForFastRewriting()) {
                            /* compute reference results using old algorithm under DEBUG mode */
                            List<Term> referenceResults = null;
                            if (ENABLE_DEBUG_MODE) {
                                referenceResults = Lists.newArrayList();
                                for (Map<Variable, Term> subst : getMatchingResults(subject, rule, termContext)) {
                                    Term ref = TermCanonicalizer.canonicalize(constructNewSubjectTerm(rule, subst, termContext), termContext);
                                    referenceResults.add(ref);
                                }

                                /* eliminate sharing of mutable terms between subject and reference results */
                                subject = DeepCloner.clone(subject);
                            }

                            Profiler.startTimer(Profiler.REWRITE_WITH_KOMPILED_RULES_TIMER);
                            succeed = KAbstractRewriteMachine.rewrite(
                                    rule,
                                    DataStructures.getCellEntry(subject),
                                    termContext);
                            if (succeed) {
                                RuleAuditing.succeed(rule);
                                if (options.experimental.trace) {
                                    System.out.println(rule);
                                }
                                Coverage.print(coverage, rule);
                                results.add(subject);

                                /* the result of rewrite machine must be in the reference results */
                                if (ENABLE_DEBUG_MODE) {
                                    assert referenceResults.contains(TermCanonicalizer.canonicalize(subject, termContext));
                                }
                            } else {
                                if (ENABLE_DEBUG_MODE) {
                                    assert referenceResults.isEmpty();
                                }
                            }
                            Profiler.stopTimer(Profiler.REWRITE_WITH_KOMPILED_RULES_TIMER);
                        } else {
                            Profiler.startTimer(Profiler.REWRITE_WITH_UNKOMPILED_RULES_TIMER);
                            for (Map<Variable, Term> subst : getMatchingResults(subject, rule, termContext)) {
                                if (options.experimental.trace) {
                                    System.out.println(rule);
                                }
                                RuleAuditing.succeed(rule);
                                Coverage.print(coverage, rule);
                                subject = constructNewSubjectTerm(rule, subst, termContext);
                                results.add(subject);
                                succeed = true;
                                break;
                            }
                            Profiler.stopTimer(Profiler.REWRITE_WITH_UNKOMPILED_RULES_TIMER);
                        }

                        if (succeed) {
                            if (rule.modifyCellStructure()) {
                                computeIndexingCells(subject, termContext);
                            }
                            return;
                        }
                    } catch (KEMException e) {
                        e.exception.addTraceFrame("while evaluating rule at " + rule.getSource() + rule.getLocation());
                        throw e;
                    } finally {
                        if (RuleAuditing.isAuditBegun()) {
                            if (RuleAuditing.getAuditingRule() == rule) {
                                RuleAuditing.endAudit();
                            }
                            if (!RuleAuditing.isSuccess()
                                    && RuleAuditing.getAuditingRule() == rule) {
                                throw RuleAuditing.fail();
                            }
                        }
                    }
                }
            }
        } finally {
            RuleAuditing.clearAuditingRule();
        }
    }

    private final Term constructNewSubjectTerm(Rule rule, Map<Variable, Term> substitution, TermContext termContext) {
        Term rhs = rule.cellsToCopy().contains(DataStructures.getCellEntry(rule.rightHandSide()).cellLabel()) ?
                DeepCloner.clone(rule.rightHandSide()) :
                rule.rightHandSide();
        Term result = rhs.copyOnShareSubstAndEval(substitution,
                rule.reusableVariables().elementSet(), termContext);
        termContext.setTopTerm(result);
        return result;
    }

    private Map<Variable, Term> getSubstitutionMap(Term term, Rule pattern, TermContext termContext) {
        List<Map<Variable, Term>> maps = PatternMatcher.match(term, pattern, termContext);
        if (maps.size() != 1) {
            return null;
        }

        Map<Variable, Term> map = maps.get(0);
        map.entrySet().forEach(e -> e.setValue(
                CellCollection.singleton(
                        CellLabel.GENERATED_TOP,
                        e.getValue(),
                        termContext.definition().context())));
        return map;
    }

    public List<Map<Variable,Term>> search(
            Term initialTerm,
            Term targetTerm,
            List<Rule> rules,
            Rule pattern,
            int bound,
            int depth,
            SearchType searchType,
            TermContext termContext) {
        stopwatch.start();

        List<Map<Variable,Term>> searchResults = new ArrayList<Map<Variable,Term>>();
        Set<Term> visited = new HashSet<Term>();

        // If depth is 0 then we are just trying to match the pattern.
        // A more clean solution would require a bit of a rework to how patterns
        // are handled in krun.Main when not doing search.
        if (depth == 0) {
            Map<Variable, Term> map = getSubstitutionMap(initialTerm, pattern, termContext);
            if (map != null) {
                searchResults.add(map);
            }
            stopwatch.stop();
            if (options.experimental.statistics) {
                System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");
            }
            return searchResults;
        }

        // The search queues will map terms to their depth in terms of transitions.
        Map<Term,Integer> queue = new LinkedHashMap<Term,Integer>();
        Map<Term,Integer> nextQueue = new LinkedHashMap<Term,Integer>();

        visited.add(initialTerm);
        queue.put(initialTerm, 0);

        if (searchType == SearchType.ONE) {
            depth = 1;
        }
        if (searchType == SearchType.STAR) {
            Map<Variable, Term> map = getSubstitutionMap(initialTerm, pattern, termContext);
            if (map != null) {
                searchResults.add(map);
            }
        }

        label:
        for (step = 0; !queue.isEmpty(); ++step) {
            for (Map.Entry<Term, Integer> entry : queue.entrySet()) {
                Term term = entry.getKey();
                Integer currentDepth = entry.getValue();
                computeSearchRewriteStep(term, -1, termContext);

                if (results.isEmpty() && searchType == SearchType.FINAL) {
                    Map<Variable, Term> map = getSubstitutionMap(term, pattern, termContext);
                    if (map != null) {
                        searchResults.add(map);
                        if (searchResults.size() == bound) {
                            break label;
                        }
                    }
                }

                for (Term result : results) {
                    if (!transition) {
                        nextQueue.put(result, currentDepth);
                        break;
                    } else {
                        // Continue searching if we haven't reached our target
                        // depth and we haven't already visited this state.
                        if (currentDepth + 1 != depth && visited.add(result)) {
                            nextQueue.put(result, currentDepth + 1);
                        }
                        // If we aren't searching for only final results, then
                        // also add this as a result if it matches the pattern.
                        if (searchType != SearchType.FINAL || currentDepth + 1 == depth) {
                            Map<Variable, Term> map = getSubstitutionMap(result, pattern, termContext);
                            if (map != null) {
                                searchResults.add(map);
                                if (searchResults.size() == bound) {
                                    break label;
                                }
                            }
                        }
                    }
                }
            }
//            System.out.println("+++++++++++++++++++++++");

            /* swap the queues */
            Map<Term, Integer> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        stopwatch.stop();
        if (options.experimental.statistics) {
            System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");
        }

        return searchResults;
    }

}

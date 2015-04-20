// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.base.Stopwatch;
import com.google.common.collect.BiMap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.inject.Inject;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.strategies.TransitionCompositeStrategy;
import org.kframework.backend.java.util.Coverage;
import org.kframework.backend.java.util.JavaKRunState;
import org.kframework.backend.java.util.JavaTransition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchType;
import org.kframework.utils.errorsystem.KEMException;

import java.util.*;
import java.util.stream.Collectors;

/**
 *
 *
 * @author AndreiS
 *
 */
public class SymbolicRewriter {

    private final Definition definition;
    private final JavaExecutionOptions javaOptions;
    private final TransitionCompositeStrategy strategy;
    private final Stopwatch stopwatch = Stopwatch.createUnstarted();
    private int step;
    private final Stopwatch ruleStopwatch = Stopwatch.createUnstarted();
    private final List<ConstrainedTerm> results = Lists.newArrayList();
    private final List<Rule> appliedRules = Lists.newArrayList();
    private final List<Map<Variable, Term>> substitutions = Lists.newArrayList();
    private KRunGraph executionGraph = null;
    private boolean transition;
    private RuleIndex ruleIndex;
    private KRunState.Counter counter;

    @Inject
    public SymbolicRewriter(Definition definition, KompileOptions kompileOptions, JavaExecutionOptions javaOptions,
                            KRunState.Counter counter) {
        this.definition = definition;
        this.javaOptions = javaOptions;
        ruleIndex = definition.getIndex();
        this.counter = counter;
        this.strategy = new TransitionCompositeStrategy(kompileOptions.transition);
    }

    public KRunGraph getExecutionGraph() {
        return executionGraph;
    }

    public KRunState rewrite(ConstrainedTerm constrainedTerm, Context context, int bound, boolean computeGraph) {
        stopwatch.start();
        KRunState initialState = null;
        if (computeGraph) {
            executionGraph = new KRunGraph();
            initialState = new JavaKRunState(constrainedTerm, context, counter);
            executionGraph.addVertex(initialState);
        }
        for (step = 0; step != bound; ++step) {
            /* get the first solution */
            computeRewriteStep(constrainedTerm, 1);
            ConstrainedTerm result = getTransition(0);
            KRunState finalState = null;
            if (result != null) {
                if (computeGraph) {
                    finalState = new JavaKRunState(result, context, counter);
                    JavaTransition javaTransition = new JavaTransition(
                            getRule(0), getSubstitution(0), context);
                    executionGraph.addEdge(javaTransition, initialState, finalState);
                    initialState = finalState;
                }
                constrainedTerm = result;
            } else {
                break;
            }
        }

        stopwatch.stop();
        if (definition.kRunOptions().experimental.statistics) {
            System.err.println("[" + step + ", " + stopwatch + "]");
        }

        if (initialState == null) {
            initialState = new JavaKRunState(constrainedTerm, context, counter);
        }
        return initialState;
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

    private ConstrainedTerm getTransition(int n) {
        return n < results.size() ? results.get(n) : null;
    }

    private Rule getRule(int n) {
        return n < appliedRules.size() ? appliedRules.get(n) : null;
    }

    private Map<Variable, Term> getSubstitution(int n) {
        return n < substitutions.size() ? substitutions.get(n) : null;
    }


    private void computeRewriteStep(ConstrainedTerm constrainedTerm) {
        computeRewriteStep(constrainedTerm, -1);
    }

    private void computeRewriteStep(ConstrainedTerm subject, int successorBound) {
        results.clear();
        appliedRules.clear();
        substitutions.clear();
        if (successorBound == 0) {
            return;
        }

        RuleAuditing.setAuditingRule(javaOptions, step, subject.termContext().definition());

        // Applying a strategy to a list of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
        strategy.reset(getRules(subject.term()));

        try {

            while (strategy.hasNext()) {
                transition = strategy.nextIsTransition();
                ArrayList<Rule> rules = Lists.newArrayList(strategy.next());
    //            System.out.println("rules.size: " + rules.size());
                for (Rule rule : rules) {
                    try {
                        ruleStopwatch.reset();
                        ruleStopwatch.start();

                        if (rule == RuleAuditing.getAuditingRule()) {
                            RuleAuditing.beginAudit();
                        } else if (RuleAuditing.isAuditBegun() && RuleAuditing.getAuditingRule() == null) {
                            System.err.println("\nAuditing " + rule + "...\n");
                        }

                        ConstrainedTerm pattern = buildPattern(rule, subject.termContext());

                        for (ConjunctiveFormula unificationConstraint : subject.unify(pattern)) {
                            RuleAuditing.succeed(rule);
                            /* compute all results */
                            ConstrainedTerm result = buildResult(rule, unificationConstraint);
                            results.add(result);
                            appliedRules.add(rule);
                            substitutions.add(unificationConstraint.substitution());
                            Coverage.print(definition.kRunOptions().experimental.coverage, subject);
                            Coverage.print(definition.kRunOptions().experimental.coverage, rule);
                            if (results.size() == successorBound) {
                                return;
                            }
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
                // If we've found matching results from one equivalence class then
                // we are done, as we can't match rules from two equivalence classes
                // in the same step.
                if (results.size() > 0) {
                    return;
                }
            }
        } finally {
            RuleAuditing.clearAuditingRule();
        }
    }

    /**
     * Builds the pattern term used in unification by composing the left-hand
     * side of a specified rule and its preconditions.
     */
    private static ConstrainedTerm buildPattern(Rule rule, TermContext context) {
        return new ConstrainedTerm(
                rule.leftHandSide(),
                ConjunctiveFormula.of(context).add(rule.lookups()).addAll(rule.requires()));
    }

    /**
     * Builds the result of rewrite by applying the resulting symbolic
     * constraint of unification to the right-hand side of the rewrite rule.
     *
     * @param rule
     *            the rewrite rule
     * @param constraint
     *            the resulting symbolic constraint of unification
     * @return the new subject term
     */
    public static ConstrainedTerm buildResult(Rule rule, ConjunctiveFormula constraint) {
        return buildResult(rule, constraint, false);
    }

    private static ConstrainedTerm buildResult(
            Rule rule,
            ConjunctiveFormula constraint,
            boolean expandPattern) {
        for (Variable variable : rule.freshConstants()) {
            constraint = constraint.add(
                    variable,
                    FreshOperations.fresh(variable.sort(), constraint.termContext()));
        }
        constraint = constraint.addAll(rule.ensures()).simplify();

        /* get fresh substitutions of rule variables */
        BiMap<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.variableSet());

        /* rename rule variables in the constraints */
        constraint = ((ConjunctiveFormula) constraint.substituteWithBinders(freshSubstitution, constraint.termContext())).simplify();

        /* rename rule variables in the rule RHS */
        Term term = rule.rightHandSide().substituteWithBinders(freshSubstitution, constraint.termContext());
        /* apply the constraints substitution on the rule RHS */
        constraint = constraint.orientSubstitution(rule.boundVariables().stream()
                .map(freshSubstitution::get)
                .collect(Collectors.toSet()));
        term = term.substituteAndEvaluate(constraint.substitution(), constraint.termContext());
        /* eliminate bindings of rule variables */
        constraint = constraint.removeBindings(freshSubstitution.values());

        ConstrainedTerm result = new ConstrainedTerm(term, constraint);
        if (expandPattern) {
            // TODO(AndreiS): move these some other place
            result = result.expandPatterns(true);
        }

        return result;
    }

    /**
     * Apply a specification rule
     */
    private ConstrainedTerm applyRule(ConstrainedTerm constrainedTerm, List<Rule> rules) {
        for (Rule rule : rules) {
            ruleStopwatch.reset();
            ruleStopwatch.start();

            ConstrainedTerm leftHandSideTerm = buildPattern(rule, constrainedTerm.termContext());
            ConjunctiveFormula constraint = constrainedTerm.matchImplies(leftHandSideTerm);
            if (constraint == null) {
                continue;
            }

            return buildResult(rule, constraint, true);
        }

        return null;
    }

    /**
     * Unifies the term with the pattern, and computes a map from variables in
     * the pattern to the terms they unify with. Adds as many search results
     * up to the bound as were found, and returns {@code true} if the bound has been reached.
     */
    private boolean addSearchResult(
            List<Substitution<Variable, Term>> searchResults,
            ConstrainedTerm initialTerm,
            Rule pattern,
            int bound) {
        assert Sets.intersection(initialTerm.term().variableSet(),
                initialTerm.constraint().substitution().keySet()).isEmpty();
        List<Substitution<Variable, Term>> discoveredSearchResults = PatternMatcher.match(
                initialTerm.term(),
                pattern,
                initialTerm.termContext());
        for (Substitution<Variable, Term> searchResult : discoveredSearchResults) {
            searchResults.add(searchResult);
            if (searchResults.size() == bound) {
                return true;
            }
        }
        return false;
    }

    /**
     *
     * @param initialTerm
     * @param targetTerm not implemented yet
     * @param rules not implemented yet
     * @param pattern the pattern we are searching for
     * @param bound a negative value specifies no bound
     * @param depth a negative value specifies no bound
     * @param searchType defines when we will attempt to match the pattern

     * @param computeGraph determines whether the transition graph should be computed.
     * @return a list of substitution mappings for results that matched the pattern
     */
    public List<Substitution<Variable,Term>> search(
            Term initialTerm,
            Term targetTerm,
            List<Rule> rules,
            Rule pattern,
            int bound,
            int depth,
            SearchType searchType,
            TermContext context,
            boolean computeGraph) {
        stopwatch.start();

        Context kilContext = context.definition().context();
        JavaKRunState startState = null;
        if (computeGraph) {
            executionGraph = new KRunGraph();
            startState = new JavaKRunState(initialTerm, kilContext, counter);
            executionGraph.addVertex(startState);
        } else {
            executionGraph = null;
        }

        List<Substitution<Variable,Term>> searchResults = Lists.newArrayList();
        Set<ConstrainedTerm> visited = Sets.newHashSet();

        ConstrainedTerm initCnstrTerm = new ConstrainedTerm(initialTerm, context);

        // If depth is 0 then we are just trying to match the pattern.
        // A more clean solution would require a bit of a rework to how patterns
        // are handled in krun.Main when not doing search.
        if (depth == 0) {
            addSearchResult(searchResults, initCnstrTerm, pattern, bound);
            stopwatch.stop();
            System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");
            return searchResults;
        }

        // The search queues will map terms to their depth in terms of transitions.
        Map<ConstrainedTerm, Integer> queue = Maps.newLinkedHashMap();
        Map<ConstrainedTerm, Integer> nextQueue = Maps.newLinkedHashMap();

        visited.add(initCnstrTerm);
        queue.put(initCnstrTerm, 0);

        if (searchType == SearchType.ONE) {
            depth = 1;
        }
        if (searchType == SearchType.STAR) {
            if (addSearchResult(searchResults, initCnstrTerm, pattern, bound)) {
                stopwatch.stop();
                System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");
                return searchResults;
            }
        }

        label:
        for (step = 0; !queue.isEmpty(); ++step) {
            for (Map.Entry<ConstrainedTerm, Integer> entry : queue.entrySet()) {
                ConstrainedTerm term = entry.getKey();
                Integer currentDepth = entry.getValue();

                if (computeGraph) {
                    startState = new JavaKRunState(term.term(), kilContext, counter);
                }

                computeRewriteStep(term);
//                    System.out.println(step);
//                    System.err.println(term);
//                    for (ConstrainedTerm r : results) {
//                        System.out.println(r);
//                    }

                if (results.isEmpty() && searchType == SearchType.FINAL) {
                    if (addSearchResult(searchResults, term, pattern, bound)) {
                        break label;
                    }
                }

                for (int resultIndex = 0; resultIndex < results.size(); resultIndex++) {
                    ConstrainedTerm result = results.get(resultIndex);
                    if (computeGraph) {
                        JavaKRunState resultState = new JavaKRunState(result.term(), kilContext, counter);
                        JavaTransition javaTransition = new JavaTransition(appliedRules.get(resultIndex),substitutions.get(resultIndex), kilContext);
                        executionGraph.addVertex(resultState);
                        executionGraph.addEdge(javaTransition, startState, resultState);
                    }
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
                            if (addSearchResult(searchResults, result, pattern, bound)) {
                                break label;
                            }
                        }
                    }
                }
            }
//                System.out.println("+++++++++++++++++++++++");

            /* swap the queues */
            Map<ConstrainedTerm, Integer> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        stopwatch.stop();
        if (definition.kRunOptions().experimental.statistics) {
            System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");
        }

        return searchResults;
    }

    public List<ConstrainedTerm> proveRule(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules) {
        List<ConstrainedTerm> proofResults = new ArrayList<>();
        Set<ConstrainedTerm> visited = new HashSet<>();
        List<ConstrainedTerm> queue = new ArrayList<>();
        List<ConstrainedTerm> nextQueue = new ArrayList<>();

        initialTerm = initialTerm.expandPatterns(true);

        visited.add(initialTerm);
        queue.add(initialTerm);
        boolean guarded = false;
        while (!queue.isEmpty()) {
            step++;
//            System.err.println("step #" + step);
            for (ConstrainedTerm term : queue) {
                if (term.implies(targetTerm)) {
                    continue;
                }

                // TODO(YilongL): the `get(0)` seems hacky
                Term leftKContent = term.term().getCellContentsByName(CellLabel.K).get(0);
                Variable leftFrame = KSequence.getFrame(leftKContent);
                if (leftFrame != null) {
                    KSequence.Builder builder = KSequence.builder();
                    KSequence.getElements(leftKContent).stream().forEach(builder::concatenate);
                    leftKContent = builder.build();
                }
                Term rightKContent = targetTerm.term().getCellContentsByName(CellLabel.K).get(0);
                Variable rightFrame = KSequence.getFrame(rightKContent);
                if (rightFrame != null) {
                    KSequence.Builder builder = KSequence.builder();
                    KSequence.getElements(rightKContent).stream().forEach(builder::concatenate);
                    rightKContent = builder.build();
                }
                if (leftFrame != null && rightFrame != null && leftFrame.equals(rightFrame)) {
                    BoolToken matchable = MetaK.matchable(
                            leftKContent,
                            rightKContent,
                            term.termContext());
                    if (matchable != null && matchable.booleanValue()) {
                        proofResults.add(term);
                        continue;
                    }
                }

                if (guarded) {
                    ConstrainedTerm result = applyRule(term, rules);
                    if (result != null) {
                        if (visited.add(result))
                            nextQueue.add(result);
                        continue;
                    }
                }

                computeRewriteStep(term);
                if (results.isEmpty()) {
                    /* final term */
                    proofResults.add(term);
                } else {
//                    for (Rule rule : appliedRules) {
//                        System.err.println(rule.getLocation() + " " + rule.getSource());
//                    }

                    /* add helper rule */
                    HashSet<Variable> ruleVariables = new HashSet<Variable>(initialTerm.variableSet());
                    ruleVariables.addAll(targetTerm.variableSet());

                    /*
                    rules.add(new Rule(
                            term.term().substitute(freshSubstitution, definition),
                            targetTerm.term().substitute(freshSubstitution, definition),
                            term.constraint().substitute(freshSubstitution, definition),
                            Collections.<Variable>emptyList(),
                            new SymbolicConstraint(definition).substitute(freshSubstitution, definition),
                            IndexingPair.getIndexingPair(term.term()),
                            new Attributes()));
                     */
                }

                for (int i = 0; getTransition(i) != null; ++i) {
                    ConstrainedTerm result = new ConstrainedTerm(
                            getTransition(i).term(),
                            getTransition(i).constraint().removeBindings(
                                    Sets.difference(
                                            getTransition(i).constraint().substitution().keySet(),
                                            initialTerm.variableSet())));
                    if (visited.add(result)) {
                        nextQueue.add(result);
                    }
                }
            }

            /* swap the queues */
            List<ConstrainedTerm> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
            guarded = true;

            /*
            for (ConstrainedTerm result : queue) {
                System.err.println(result);
            }
            System.err.println("============================================================");
             */
        }

        return proofResults;
    }

}

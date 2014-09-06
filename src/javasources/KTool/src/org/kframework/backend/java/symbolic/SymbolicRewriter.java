// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.indexing.Index;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.kil.*;
import org.kframework.utils.general.IndexingStatistics;
import org.kframework.backend.java.strategies.TransitionCompositeStrategy;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.api.SearchType;
import org.kframework.krun.api.io.FileSystem;

import com.google.common.base.Stopwatch;
import com.google.inject.Inject;

/**
 *
 *
 * @author AndreiS
 *
 */
public class SymbolicRewriter {

    private final Definition definition;
    private final TransitionCompositeStrategy strategy;
    private final Stopwatch stopwatch = Stopwatch.createUnstarted();
    private int step;
    private final Stopwatch ruleStopwatch = Stopwatch.createUnstarted();
    private final List<ConstrainedTerm> results = new ArrayList<ConstrainedTerm>();
    private final List<Rule> appliedRules = new ArrayList<Rule>();
    private boolean transition;
    private RuleIndex ruleIndex;
    private final boolean indexingStats;

    /*
     * Liyi Li : add simulation rules in the constructor, and allow user to input label [alphaRule] as
     * the indication that the rule will be used as simulation
     */
    @Inject
    public SymbolicRewriter(Definition definition, KompileOptions kompileOptions, JavaExecutionOptions javaOptions) {
        this.definition = definition;
        this.indexingStats = javaOptions.indexingStats;
        ruleIndex = definition.getIndex();

        this.strategy = new TransitionCompositeStrategy(kompileOptions.transition);
    }

    public ConstrainedTerm rewrite(ConstrainedTerm constrainedTerm, int bound) {
        stopwatch.start();

        for (step = 0; step != bound; ++step) {
            /* get the first solution */
            computeRewriteStep(constrainedTerm, 1);
            ConstrainedTerm result = getTransition(0);
            if (result != null) {
                constrainedTerm = result;
            } else {
                break;
            }
        }

        stopwatch.stop();
        System.err.println("[" + step + ", " + stopwatch + "]");

        return constrainedTerm;
    }

    public ConstrainedTerm rewrite(ConstrainedTerm constrainedTerm) {
        return rewrite(constrainedTerm, -1);
    }

    /* author: Liyi Li
     * a function return all the next steps of a given term
     */
    public ArrayList<ConstrainedTerm> rewriteAll(ConstrainedTerm constrainedTerm){

        computeRewriteStep(constrainedTerm);

        return (ArrayList<ConstrainedTerm>) results;
    }

    /*
     * author: Liyi Li
     * return the rules for simulations only
     */
    public Map<Index, List<Rule>> getSimulationMap(){
        return ((IndexingTable) ruleIndex).getSimulationRuleTable();
    }

    /*
     * author: Liyi Li
     * return the rules for simulations only
     */
    private List<Rule> getSimulationRules(Term term) {
        List<Rule> rules = new ArrayList<Rule>();
        for (IndexingPair pair : term.getKCellIndexingPairs(definition)) {
            if (((IndexingTable) ruleIndex).getSimulationRuleTable().get(pair.first) != null) {
                rules.addAll(((IndexingTable) ruleIndex).getSimulationRuleTable().get(pair.first));
            }
        }
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
        List<Rule> rules = new ArrayList<>();
        if (indexingStats){
            IndexingStatistics.getRulesForTermStopWatch.reset();
            IndexingStatistics.getRulesForTermStopWatch.start();
        }

        rules.addAll(ruleIndex.getRules(term));

        if (indexingStats){
            IndexingStatistics.rulesSelectedAtEachStep.add(rules.size());
            long elapsed =
                    IndexingStatistics.getRulesForTermStopWatch.stop().elapsed(TimeUnit.MICROSECONDS);
            IndexingStatistics.timesForRuleSelection.add(elapsed);
        }
        return rules;
    }

    private ConstrainedTerm getTransition(int n) {
        return n < results.size() ? results.get(n) : null;
    }

    /*
     * author : Liyi Li
     * computer steps by rules of simulation
     */
    @SuppressWarnings("unchecked")
    public ConstrainedTerm computeSimulationStep(ConstrainedTerm constrainedTerm) {
        // Applying a strategy to a list of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
        //        System.out.println(LookupCell.find(constrainedTerm.term(),"k"));
        strategy.reset(getSimulationRules(constrainedTerm.term()));
        while (strategy.hasNext()) {
            transition = strategy.nextIsTransition();
            List<Rule> rules = ((List<Rule>)strategy.next());

            for (Rule rule : rules) {
                ruleStopwatch.reset();
                ruleStopwatch.start();

                SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(
                        constrainedTerm.termContext());
                leftHandSideConstraint.addAll(rule.requires());

                CellCollection newTemp = CellCollection.singleton((Cell<Term>)rule.leftHandSide(), definition.context());

                Cell<Term> newRuleTerm = new Cell<Term>(CellLabel.GENERATED_TOP, newTemp);

                ConstrainedTerm leftHandSideTerm = new ConstrainedTerm(
                        newRuleTerm,
                        rule.lookups().getSymbolicConstraint(constrainedTerm.termContext()),
                        leftHandSideConstraint,
                        constrainedTerm.termContext());

                SymbolicConstraint constraint = constrainedTerm.matchImplies(leftHandSideTerm);
                if (constraint == null) {
                    continue;
                }
                constraint.addAll(rule.ensures());

                /* rename rule variables in the constraints */
                Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());

                Term result = rule.rightHandSide();
                /* rename rule variables in the rule RHS */
                result = result.substituteWithBinders(freshSubstitution, constrainedTerm.termContext());
                /* apply the constraints substitution on the rule RHS */
                result = result.substituteWithBinders(constraint.substitution(), constrainedTerm.termContext());
                /* evaluate pending functions in the rule RHS */
                //result = result.evaluate(constrainedTerm.termContext());
                /* eliminate anonymous variables */
                constraint.eliminateAnonymousVariables(constrainedTerm.variableSet());

                /* return first solution */
                return new ConstrainedTerm(result, constraint, constrainedTerm.termContext());
            }

        }
        //System.out.println("Result: " + results.toString());
        //System.out.println();

        return null;
    }

    private void computeRewriteStep(ConstrainedTerm constrainedSubject, int successorBound) {
        int rulesTried = 0;
        if (indexingStats){
            IndexingStatistics.rewriteStepStopWatch.reset();
            IndexingStatistics.rewriteStepStopWatch.start();
        }
        results.clear();
        appliedRules.clear();

        if (successorBound == 0) {
            return;
        }

        // Applying a strategy to a list of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
        //        System.out.println(LookupCell.find(constrainedTerm.term(),"k"));
        strategy.reset(getRules(constrainedSubject.term()));

        while (strategy.hasNext()) {
            if (indexingStats){
                IndexingStatistics.rewritingStopWatch.reset();
                IndexingStatistics.rewritingStopWatch.start();
            }
            transition = strategy.nextIsTransition();
            ArrayList<Rule> rules = new ArrayList<Rule>(strategy.next());
//            System.out.println("rules.size: "+rules.size());
            for (Rule rule : rules) {
                rulesTried++;
                ruleStopwatch.reset();
                ruleStopwatch.start();

                ConstrainedTerm constrainedPattern = preparePattern(rule, constrainedSubject.termContext());

                for (SymbolicConstraint constraint1 : getUnificationResults(constrainedSubject, constrainedPattern)) {
                    /* compute all results */
                    ConstrainedTerm newCnstrTerm = constructNewSubjectTerm(
                            rule,
                            constraint1,
                            constrainedSubject.variableSet());
                    // TODO(YilongL): the following assertion is not always true; fix it
//                    if (K.do_concrete_exec) {
//                        assert newCnstrTerm.isGround();
//                    }
                    results.add(newCnstrTerm);
                    appliedRules.add(rule);
                    if (indexingStats){
                        IndexingStatistics.rulesTried.add(rulesTried);
                        if (IndexingStatistics.rewritingStopWatch.isRunning()){
                            IndexingStatistics.rewritingStopWatch.stop();
                        }
                        IndexingStatistics.timesForRewriting.add(
                                IndexingStatistics.rewritingStopWatch.elapsed(TimeUnit.MICROSECONDS));
                    }
                    if (results.size() == successorBound) {
                        if (indexingStats) {
                            IndexingStatistics.rewriteStepStopWatch.stop();
                            long elapsed =
                                    IndexingStatistics.rewriteStepStopWatch.elapsed(TimeUnit.MICROSECONDS);
                            IndexingStatistics.timesForRewriteSteps.add(elapsed);
                        }
                        return;
                    }
                }
            }
            // If we've found matching results from one equivalence class then
            // we are done, as we can't match rules from two equivalence classes
            // in the same step.
            if (results.size() > 0) {
                //TODO(OwolabiL): Remove duplication
                if (indexingStats){
                    IndexingStatistics.rewriteStepStopWatch.stop();
                    long elapsed =
                            IndexingStatistics.rewriteStepStopWatch.elapsed(TimeUnit.MICROSECONDS);
                    IndexingStatistics.timesForRewriteSteps.add(elapsed);
                }
                return;
            }
        }
        //System.out.println("Result: " + results.toString());
        //System.out.println();
    }

    private void computeRewriteStep(ConstrainedTerm constrainedTerm) {
        computeRewriteStep(constrainedTerm, -1);
    }

    /**
     * Prepares the pattern term used in unification by composing the left-hand
     * side of a specified rule and its side-conditions.
     *
     * @param rule
     *            the specified rule
     * @param termContext
     *            the term context
     * @return the pattern term
     */
    private ConstrainedTerm preparePattern(Rule rule, TermContext termContext) {
        SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(
                termContext);
        leftHandSideConstraint.addAll(rule.requires());
        for (Variable variable : rule.freshVariables()) {
            leftHandSideConstraint.add(
                    variable,
                    FreshOperations.fresh(variable.sort(), termContext));
        }

        ConstrainedTerm leftHandSide = new ConstrainedTerm(
                rule.leftHandSide(),
                rule.lookups().getSymbolicConstraint(termContext),
                leftHandSideConstraint,
                termContext);
        return leftHandSide;
    }

    /**
     * Constructs the new subject term by applying the resulting symbolic
     * constraint of unification to the right-hand side of the rewrite rule.
     *
     * @param rule
     *            the rewrite rule
     * @param constraint
     *            a symbolic constraint between the left-hand side of the
     *            rewrite rule and the current subject term
     * @return the new subject term
     */
    public static ConstrainedTerm constructNewSubjectTerm(
            Rule rule,
            SymbolicConstraint constraint,
            Set<Variable> existingVariables) {
        /*
         * TODO(YilongL): had to comment out the following assertion because
         * logik.k uses unification even in concrete execution mode
         */
        // if (K.do_concrete_exec) {
        // assert constraint1.isMatching(leftHandSide) :
        // "Pattern matching expected in concrete execution mode";
        // }
        constraint.orientSubstitution(rule.leftHandSide().variableSet());
        constraint.addAll(rule.ensures());

        Term result = rule.rightHandSide();

        /* rename rule variables in the constraints */
        Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());
        /* rename rule variables in the rule RHS */
        result = result.substituteWithBinders(freshSubstitution, constraint.termContext());
        /* apply the constraints substitution on the rule RHS */
        result = result.substituteAndEvaluate(
                constraint.substitution(),
                constraint.termContext());
        /* eliminate anonymous variables */
        constraint.eliminateAnonymousVariables(existingVariables);
        // TODO(AndreiS): functions not being evaluated is becoming quite annoying
        result = result.evaluate(constraint.termContext());

        /*
        System.err.println("rule \n\t" + rule);
        System.err.println("result term\n\t" + result);
        System.err.println("result constraint\n\t" + constraint1);
        System.err.println("============================================================");
         */
        return new ConstrainedTerm(result, constraint, constraint.termContext());
    }

    /**
     * Returns a list of symbolic constraints obtained by unifying the two
     * constrained terms.
     * <p>
     * This method is extracted to simplify the profiling script.
     * </p>
     */
    private List<SymbolicConstraint> getUnificationResults(
            ConstrainedTerm constrainedTerm,
            ConstrainedTerm otherConstrainedTerm) {
        return constrainedTerm.unify(otherConstrainedTerm);
    }

    /**
     * Apply a specification rule
     */
    private ConstrainedTerm applyRule(ConstrainedTerm constrainedTerm, List<Rule> rules) {
        for (Rule rule : rules) {
            ruleStopwatch.reset();
            ruleStopwatch.start();

            SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(
                    constrainedTerm.termContext());
            leftHandSideConstraint.addAll(rule.requires());

            ConstrainedTerm leftHandSideTerm = new ConstrainedTerm(
                    rule.leftHandSide(),
                    rule.lookups().getSymbolicConstraint(constrainedTerm.termContext()),
                    leftHandSideConstraint,
                    constrainedTerm.termContext());

            SymbolicConstraint constraint = constrainedTerm.matchImplies(leftHandSideTerm);
            if (constraint == null) {
                continue;
            }
            constraint.addAllThenSimplify(rule.ensures());

            /* rename rule variables in the constraints */
            Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());

            Term result = rule.rightHandSide();
            /* rename rule variables in the rule RHS */
            result = result.substituteWithBinders(freshSubstitution, constrainedTerm.termContext());
            /* apply the constraints substitution on the rule RHS */
            result = result.substituteWithBinders(constraint.substitution(), constrainedTerm.termContext());
            /* evaluate pending functions in the rule RHS */
            result = result.evaluate(constrainedTerm.termContext());
            /* eliminate anonymous variables */
            constraint.eliminateAnonymousVariables(constrainedTerm.variableSet());

            // TODO(AndreiS): move these some other place
            constraint.expandPatternsAndSimplify(true);
            result = result.expandPatterns(constraint, true, constrainedTerm.termContext());

            /* return first solution */
            return new ConstrainedTerm(result, constraint, constrainedTerm.termContext());
        }

        return null;
    }

    // Unifies the term with the pattern, and returns a map from variables in
    // the pattern to the terms they unify with. Returns null if the term
    // can't be unified with the pattern.
    private Map<Variable, Term> getSubstitutionMap(ConstrainedTerm term, Rule pattern) {
        // Create the initial constraints based on the pattern
        SymbolicConstraint termConstraint = new SymbolicConstraint(term.termContext());
        termConstraint.addAll(pattern.requires());
        for (Variable var : pattern.freshVariables()) {
            termConstraint.add(var, FreshOperations.fresh(var.sort(), term.termContext()));
        }

        // Create a constrained term from the left hand side of the pattern.
        ConstrainedTerm lhs = new ConstrainedTerm(
                pattern.leftHandSide(),
                pattern.lookups().getSymbolicConstraint(term.termContext()),
                termConstraint,
                term.termContext());

        // Collect the variables we are interested in finding
        VariableCollector visitor = new VariableCollector();
        lhs.accept(visitor);

        Collection<SymbolicConstraint> constraints = getUnificationResults(term, lhs);
        if (constraints.isEmpty()) {
            return null;
        }

        // Build a substitution map containing the variables in the pattern from
        // the substitution constraints given by unification.
        Map<Variable, Term> map = new HashMap<Variable, Term>();
        for (SymbolicConstraint constraint : constraints) {
            if (!constraint.isSubstitution()) {
                return null;
            }
            constraint.orientSubstitution(visitor.getVariableSet());
            for (Variable variable : visitor.getVariableSet()) {
                Term value = constraint.substitution().get(variable);
                if (value == null) {
                    return null;
                }
                map.put(variable, new Cell<Term>(CellLabel.GENERATED_TOP, value));
            }
        }
        return map;
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

     * @return a list of substitution mappings for results that matched the pattern
     */
    public List<Map<Variable,Term>> search(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules,
            Rule pattern,
            int bound,
            int depth,
            SearchType searchType) {
        stopwatch.start();

        List<Map<Variable,Term>> searchResults = new ArrayList<Map<Variable,Term>>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();

        // If depth is 0 then we are just trying to match the pattern.
        // A more clean solution would require a bit of a rework to how patterns
        // are handled in krun.Main when not doing search.
        if (depth == 0) {
            Map<Variable, Term> map = getSubstitutionMap(initialTerm, pattern);
            if (map != null) {
                searchResults.add(map);
            }
            stopwatch.stop();
            System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");
            return searchResults;
        }

        // The search queues will map terms to their depth in terms of transitions.
        Map<ConstrainedTerm,Integer> queue = new LinkedHashMap<ConstrainedTerm,Integer>();
        Map<ConstrainedTerm,Integer> nextQueue = new LinkedHashMap<ConstrainedTerm,Integer>();

        visited.add(initialTerm);
        queue.put(initialTerm, 0);

        if (searchType == SearchType.ONE) {
            depth = 1;
        }
        if (searchType == SearchType.STAR) {
            Map<Variable, Term> map = getSubstitutionMap(initialTerm, pattern);
            if (map != null) {
                searchResults.add(map);
            }
        }

        label:
        for (step = 0; !queue.isEmpty(); ++step) {
            for (Map.Entry<ConstrainedTerm, Integer> entry : queue.entrySet()) {
                ConstrainedTerm term = entry.getKey();
                Integer currentDepth = entry.getValue();
                computeRewriteStep(term);
//                    System.out.println(step);
//                    System.err.println(term);
//                    for (ConstrainedTerm r : results) {
//                        System.out.println(r);
//                    }

                if (results.isEmpty() && searchType == SearchType.FINAL) {
                    Map<Variable, Term> map = getSubstitutionMap(term, pattern);
                    if (map != null) {
                        searchResults.add(map);
                        if (searchResults.size() == bound) {
                            break label;
                        }
                    }
                }

                for (ConstrainedTerm result : results) {
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
                            Map<Variable, Term> map = getSubstitutionMap(result, pattern);
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
//                System.out.println("+++++++++++++++++++++++");

                /* swap the queues */
            Map<ConstrainedTerm, Integer> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");

        return searchResults;
    }


    public List<ConstrainedTerm> prove(List<Rule> rules, FileSystem fs, TermContext context) {
        stopwatch.start();

        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();
        for (Rule rule : rules) {
            /* rename rule variables */
            Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.variableSet());

            SymbolicConstraint sideConstraint = new SymbolicConstraint(context);
            sideConstraint.addAll(rule.requires());
            ConstrainedTerm initialTerm = new ConstrainedTerm(
                    rule.leftHandSide().substituteWithBinders(freshSubstitution, context),
                    rule.lookups().getSymbolicConstraint(context).substituteWithBinders(
                            freshSubstitution,
                            context),
                    sideConstraint.substituteWithBinders(freshSubstitution, context),
                    context);

            ConstrainedTerm targetTerm = new ConstrainedTerm(
                    rule.rightHandSide().substituteWithBinders(freshSubstitution, context),
                    context);

            proofResults.addAll(proveRule(initialTerm, targetTerm, rules));
        }

        stopwatch.stop();
        System.err.println("[" + stopwatch + "]");

        return proofResults;
    }

    public List<ConstrainedTerm> proveRule(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules) {
        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();
        List<ConstrainedTerm> queue = new ArrayList<ConstrainedTerm>();
        List<ConstrainedTerm> nextQueue = new ArrayList<ConstrainedTerm>();

        initialTerm = new ConstrainedTerm(
                initialTerm.term().expandPatterns(
                        initialTerm.constraint(),
                        true,
                        initialTerm.termContext()),
                initialTerm.constraint(),
                initialTerm.termContext());

        visited.add(initialTerm);
        queue.add(initialTerm);
        boolean guarded = false;
        while (!queue.isEmpty()) {
            step++;
            for (ConstrainedTerm term : queue) {
                if (term.implies(targetTerm)) {
                    continue;
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
                    /* add helper rule */
                    HashSet<Variable> ruleVariables = new HashSet<Variable>(initialTerm.variableSet());
                    ruleVariables.addAll(targetTerm.variableSet());
                    Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(
                            ruleVariables);

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
                    if (visited.add(getTransition(i))) {
                        nextQueue.add(getTransition(i));
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

    public Definition getDefinition() {
        return definition;
    }

}

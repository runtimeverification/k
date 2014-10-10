// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.strategies.TransitionCompositeStrategy;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.api.SearchType;

import com.google.common.base.Stopwatch;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.inject.Inject;

/**
 *
 *
 * @author AndreiS
 *
 */
public class SymbolicRewriter {

    private final Definition definition; // TODO(YilongL): use TermContext instead
    private final TransitionCompositeStrategy strategy;
    private final Stopwatch stopwatch = Stopwatch.createUnstarted();
    private int step;
    private final Stopwatch ruleStopwatch = Stopwatch.createUnstarted();
    private final List<ConstrainedTerm> results = Lists.newArrayList();
    private final List<Rule> appliedRules = Lists.newArrayList();
    private boolean transition;
    private RuleIndex ruleIndex;

    @Inject
    public SymbolicRewriter(Definition definition, KompileOptions kompileOptions, JavaExecutionOptions javaOptions) {
        this.definition = definition;
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
        if (definition.context().krunOptions.experimental.statistics) {
            System.err.println("[" + step + ", " + stopwatch + "]");
        }

        return constrainedTerm;
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

    private void computeRewriteStep(ConstrainedTerm constrainedTerm) {
        computeRewriteStep(constrainedTerm, -1);
    }

    private void computeRewriteStep(ConstrainedTerm subject, int successorBound) {
        results.clear();
        appliedRules.clear();

        if (successorBound == 0) {
            return;
        }

        // Applying a strategy to a list of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
        strategy.reset(getRules(subject.term()));

        while (strategy.hasNext()) {
            transition = strategy.nextIsTransition();
            ArrayList<Rule> rules = Lists.newArrayList(strategy.next());
//            System.out.println("rules.size: " + rules.size());
            for (Rule rule : rules) {
                ruleStopwatch.reset();
                ruleStopwatch.start();

                ConstrainedTerm pattern = buildPattern(rule, subject.termContext());

                for (SymbolicConstraint unifConstraint : subject.unify(pattern)) {
                    /* compute all results */
                    ConstrainedTerm result = buildResult(
                            rule,
                            unifConstraint);
                    results.add(result);
                    appliedRules.add(rule);
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

    /**
     * Builds the pattern term used in unification by composing the left-hand
     * side of a specified rule and its preconditions.
     *
     * @param rule
     *            the specified rule
     * @param termContext
     *            the term context
     * @return the pattern term
     */
    private ConstrainedTerm buildPattern(Rule rule, TermContext termContext) {
        SymbolicConstraint precondition = new SymbolicConstraint(termContext);
        precondition.addAll(rule.requires());

        ConstrainedTerm pattern = new ConstrainedTerm(
                rule.leftHandSide(),
                rule.lookups().getSymbolicConstraint(termContext),
                precondition,
                termContext);
        return pattern;
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
    public static ConstrainedTerm buildResult(
            Rule rule,
            SymbolicConstraint constraint) {
        constraint.orientSubstitution(rule.leftHandSide().variableSet());
        for (Variable variable : rule.freshVariables()) {
            constraint.add(variable, FreshOperations.fresh(variable.sort(), constraint.termContext()));
        }
        constraint.addAll(rule.ensures());

        Term term = rule.rightHandSide();

        /* get fresh substitutions of rule variables */
        Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.variableSet());

        /* rename rule variables in the constraints */
//        constraint = (SymbolicConstraint) constraint.substituteWithBinders(freshSubstitution, constraint.termContext());
        constraint.rename(freshSubstitution);

        /* rename rule variables in the rule RHS */
        term = term.substituteWithBinders(freshSubstitution, constraint.termContext());
        /* apply the constraints substitution on the rule RHS */
        term = term.substituteAndEvaluate(
                constraint.substitution(),
                constraint.termContext());
        /* eliminate bindings of rule variables */
        constraint.removeBindings(freshSubstitution.values());
        // TODO(AndreiS): functions not being evaluated is becoming quite annoying
        // TODO(YilongL): figure out why and then remove the following defensive code
        term = term.evaluate(constraint.termContext());

        return new ConstrainedTerm(term, constraint, constraint.termContext());
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

            /* get fresh substitutions of rule variables */
            Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.variableSet());

            /* rename rule variables in the constraints */
//            constraint = (SymbolicConstraint) constraint.substituteWithBinders(freshSubstitution, constraint.termContext());
            constraint.rename(freshSubstitution);

            /* rename rule variables in the rule RHS */
            Term result = rule.rightHandSide().substituteWithBinders(freshSubstitution, constrainedTerm.termContext());
            /* apply the constraints substitution on the rule RHS */
            result = result.substituteWithBinders(constraint.substitution(), constrainedTerm.termContext());
            /* evaluate pending functions in the rule RHS */
            result = result.evaluate(constrainedTerm.termContext());
            /* eliminate bindings of rule variables */
            constraint.removeBindings(freshSubstitution.values());

            // TODO(AndreiS): move these some other place
            constraint.expandPatternsAndSimplify(true);
            result = result.expandPatterns(constraint, true, constrainedTerm.termContext());

            /* return first solution */
//            System.err.println(rule.getLocation() + " " + rule.getSource());
            return new ConstrainedTerm(result, constraint, constrainedTerm.termContext());
        }

        return null;
    }

    /**
     * Unifies the term with the pattern, and returns a map from variables in
     * the pattern to the terms they unify with. Returns {@code null} if the
     * term can't be unified with the pattern.
     */
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

        Collection<SymbolicConstraint> constraints = term.unify(lhs);
        if (constraints.isEmpty()) {
            return null;
        }

        // Build a substitution map containing the variables in the pattern from
        // the substitution constraints given by unification.
        Map<Variable, Term> map = Maps.newHashMap();
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
                map.put(variable, new Cell<>(CellLabel.GENERATED_TOP, value));
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

        List<Map<Variable,Term>> searchResults = Lists.newArrayList();
        Set<ConstrainedTerm> visited = Sets.newHashSet();

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
        Map<ConstrainedTerm,Integer> queue = Maps.newLinkedHashMap();
        Map<ConstrainedTerm,Integer> nextQueue = Maps.newLinkedHashMap();

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
        if (definition.context().krunOptions.experimental.statistics) {
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
//            System.err.println("step #" + step);
            for (ConstrainedTerm term : queue) {
                if (term.implies(targetTerm)) {
                    continue;
                }

                // TODO(YilongL): the `get(0)` seems hacky
                Term leftKContent = term.term().getCellContentsByName(CellLabel.K).get(0);
                Variable leftFrame = KSequence.getFrame(leftKContent);
                Term rightKContent = targetTerm.term().getCellContentsByName(CellLabel.K).get(0);
                Variable rightFrame = KSequence.getFrame(rightKContent);
                if (leftFrame != null && rightFrame != null && leftFrame.equals(rightFrame)) {
                    BoolToken unifiable = MetaK.unifiable(
                            leftKContent,
                            rightKContent,
                            term.termContext());
                    if (unifiable != null && unifiable.booleanValue()) {
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
                    Variable.getFreshSubstitution(ruleVariables);

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

}

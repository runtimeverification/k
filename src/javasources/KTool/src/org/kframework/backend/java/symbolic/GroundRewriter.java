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

import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.krun.api.SearchType;

import com.google.common.base.Stopwatch;

public class GroundRewriter extends AbstractRewriter {
    
    private final Stopwatch stopwatch = new Stopwatch();
    private boolean transition;

    public GroundRewriter(Definition definition, TermContext termContext) {
        super(definition, termContext);
    }

    @Override
    public Term rewrite(Term subject, int bound) {
        stopwatch.start();

        subject = super.rewrite(subject, bound);
        
        stopwatch.stop();
        System.err.println("[" + step + ", " + stopwatch + "]");

        return subject;
    }

    @Override
    protected final void computeRewriteStep(Term subject, int successorBound) {
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
                for (Map<Variable, Term> subst : getMatchingResults(subject, rule)) {
                    results.add(constructNewSubjectTerm(rule, subst));
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
    
    @Override
    protected Term constructNewSubjectTerm(Rule rule, Map<Variable, Term> substitution) {
        return rule.rightHandSide().substituteAndEvaluate(substitution, termContext);
    }

    // Unifies the term with the pattern, and returns a map from variables in
    // the pattern to the terms they unify with. Returns null if the term
    // can't be unified with the pattern.
    private Map<Variable, Term> getSubstitutionMap(Term term, Rule pattern) {
        // Create the initial constraints based on the pattern
        SymbolicConstraint termConstraint = new SymbolicConstraint(termContext);
        termConstraint.addAll(pattern.requires());
        for (Variable var : pattern.freshVariables()) {
            termConstraint.add(var, FreshOperations.fresh(var.sort(), termContext));
        }

        // Create a constrained term from the left hand side of the pattern.
        ConstrainedTerm lhs = new ConstrainedTerm(
                pattern.leftHandSide(),
                pattern.lookups().getSymbolicConstraint(termContext),
                termConstraint,
                termContext);

        // Collect the variables we are interested in finding
        VariableCollector visitor = new VariableCollector();
        lhs.accept(visitor);

        ConstrainedTerm cnstrTerm = new ConstrainedTerm(term, termContext);
        Collection<SymbolicConstraint> constraints = cnstrTerm.unify(lhs);
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
                map.put(variable, new Cell<Term>("generatedTop", value));
            }
        }
        return map;
    }

    @Override
    public List<Map<Variable,Term>> search(
            Term initialTerm,
            Term targetTerm,
            List<Rule> rules,
            Rule pattern,
            int bound,
            int depth,
            SearchType searchType) {
        stopwatch.start();

        List<Map<Variable,Term>> searchResults = new ArrayList<Map<Variable,Term>>();
        Set<Term> visited = new HashSet<Term>();

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
        Map<Term,Integer> queue = new LinkedHashMap<Term,Integer>();
        Map<Term,Integer> nextQueue = new LinkedHashMap<Term,Integer>();

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
            for (Map.Entry<Term, Integer> entry : queue.entrySet()) {
                Term term = entry.getKey();
                Integer currentDepth = entry.getValue();
                computeRewriteStep(term);

                if (results.isEmpty() && searchType == SearchType.FINAL) {
                    Map<Variable, Term> map = getSubstitutionMap(term, pattern);
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
//            System.out.println("+++++++++++++++++++++++");

            /* swap the queues */
            Map<Term, Integer> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");

        return searchResults;
    }
}

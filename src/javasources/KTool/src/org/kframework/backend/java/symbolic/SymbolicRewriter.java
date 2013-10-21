package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableMap;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.indexing.BottomIndex;
import org.kframework.backend.java.indexing.FreezerIndex;
import org.kframework.backend.java.indexing.Index;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.indexing.KLabelIndex;
import org.kframework.backend.java.indexing.TokenIndex;
import org.kframework.backend.java.indexing.TopIndex;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.LookupCell;
import org.kframework.krun.api.io.FileSystem;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Stopwatch;
import com.google.common.collect.ImmutableSet;


/**
 *
 *
 * @author AndreiS
 */
public class SymbolicRewriter {

    private final Definition definition;
    private final Stopwatch stopwatch = new Stopwatch();
    private int step;
    private final Stopwatch ruleStopwatch = new Stopwatch();
    private final Map<IndexingPair, Set<Rule>> ruleTable;
    private final Set<Rule> unindexedRules;
    private final List<ConstrainedTerm> results = new ArrayList<ConstrainedTerm>();

	public SymbolicRewriter(Definition definition) {
        this.definition = definition;

        /* populate the table of rules rewriting the top configuration */
        Set<Index> indices = new HashSet<Index>();
        indices.add(TopIndex.TOP);
        indices.add(BottomIndex.BOTTOM);
        for (KLabelConstant kLabel : definition.kLabels()) {
            indices.add(new KLabelIndex(kLabel));
            indices.add(new FreezerIndex(kLabel, -1));
            if (!kLabel.productions().isEmpty()) {
                for (int i = 0; i < kLabel.productions().get(0).getArity(); ++i) {
                    indices.add(new FreezerIndex(kLabel, i));
                }
            }
        }
        //for (KLabelConstant frozenKLabel : definition.frozenKLabels()) {
        //    for (int i = 0; i < frozenKLabel.productions().get(0).getArity(); ++i) {
        //        indices.add(new FreezerIndex(frozenKLabel, i));
        //    }
        //}
        for (String sort : Definition.TOKEN_SORTS) {
            indices.add(new TokenIndex(sort));
        }

        ImmutableMap.Builder<IndexingPair, Set<Rule>> mapBuilder = ImmutableMap.builder();
        for (Index first : indices) {
            for (Index second : indices) {
                IndexingPair pair = new IndexingPair(first, second);

                ImmutableSet.Builder<Rule> setBuilder = ImmutableSet.builder();
                for (Rule rule : definition.rules()) {
                    if (pair.isUnifiable(rule.indexingPair())) {
                        setBuilder.add(rule);
                    }
                }

                ImmutableSet<Rule> rules = setBuilder.build();
                if (!rules.isEmpty()) {
                    mapBuilder.put(pair, rules);
                }
            }
        }

        ruleTable = mapBuilder.build();

        ImmutableSet.Builder<Rule> setBuilder = ImmutableSet.builder();
        for (Rule rule : definition.rules()) {
            if (!rule.containsKCell()) {
                setBuilder.add(rule);
            }
        }
        unindexedRules = setBuilder.build();
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

    private Set<Rule> getRules(Term term) {
        Set<Rule> rules = new HashSet<Rule>();
        for (IndexingPair pair : term.getIndexingPairs()) {
            if (ruleTable.get(pair) != null) {
                rules.addAll(ruleTable.get(pair));
            }
        }
        rules.addAll(unindexedRules);
        return rules;
    }

    private ConstrainedTerm getTransition(int n) {
        return n < results.size() ? results.get(n) : null;
    }

    private void computeRewriteStep(ConstrainedTerm constrainedTerm, int successorBound) {
        results.clear();

        if (successorBound == 0) {
            return;
        }

        for (Rule rule : getRules(constrainedTerm.term())) {
            ruleStopwatch.reset();
            ruleStopwatch.start();

            SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(
                constrainedTerm.termContext());
            leftHandSideConstraint.addAll(rule.condition());
            for (Variable variable : rule.freshVariables()) {
                leftHandSideConstraint.add(variable, IntToken.fresh());
            }

            ConstrainedTerm leftHandSide = new ConstrainedTerm(
                    rule.leftHandSide(),
                    rule.lookups().getSymbolicConstraint(constrainedTerm.termContext()),
                    leftHandSideConstraint,
                    constrainedTerm.termContext());

            for (SymbolicConstraint constraint1 : constrainedTerm.unify(leftHandSide)) {
                /* rename rule variables in the constraints */
                Map<Variable, Variable> freshSubstitution = constraint1.rename(rule.variableSet());

                Term result = rule.rightHandSide();
                /* rename rule variables in the rule RHS */
                result = result.substitute(freshSubstitution, constrainedTerm.termContext());
                /* apply the constraints substitution on the rule RHS */
                result = result.substituteAndEvaluate(constraint1.substitution(),
                    constrainedTerm.termContext());
                /* evaluate pending functions in the rule RHS */
//                result = result.evaluate(constrainedTerm.termContext());
                /* eliminate anonymous variables */
                constraint1.eliminateAnonymousVariables();

                /*
                System.err.println("rule \n\t" + rule);
                System.err.println("result term\n\t" + result);
                System.err.println("result constraint\n\t" + constraint1);
                System.err.println("============================================================");
                */

                /* compute all results */
                results.add(new ConstrainedTerm(result, constraint1,
                    constrainedTerm.termContext()));

                if (results.size() == successorBound) {
                    return;
                }
            }
        }
        //System.out.println("Result: " + results.toString());
        //System.out.println();
    }

    private void computeRewriteStep(ConstrainedTerm constrainedTerm) {
        computeRewriteStep(constrainedTerm, -1);
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
            leftHandSideConstraint.addAll(rule.condition());

            ConstrainedTerm leftHandSideTerm = new ConstrainedTerm(
                    rule.leftHandSide(),
                    rule.lookups().getSymbolicConstraint(constrainedTerm.termContext()),
                    leftHandSideConstraint,
                    constrainedTerm.termContext());

            SymbolicConstraint constraint = constrainedTerm.matchImplies(leftHandSideTerm);
            if (constraint == null) {
                continue;
            }

            /* rename rule variables in the constraints */
            Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());

            Term result = rule.rightHandSide();
            /* rename rule variables in the rule RHS */
            result = result.substitute(freshSubstitution, constrainedTerm.termContext());
            /* apply the constraints substitution on the rule RHS */
            result = result.substitute(constraint.substitution(), constrainedTerm.termContext());
            /* evaluate pending functions in the rule RHS */
            result = result.evaluate(constrainedTerm.termContext());
            /* eliminate anonymous variables */
            constraint.eliminateAnonymousVariables();

            /* return first solution */
            return new ConstrainedTerm(result, constraint, constrainedTerm.termContext());
        }

        return null;
    }

    /**
     *
     * @param initialTerm
     * @param targetTerm not implemented yet
     * @param rules not implemented yet
     * @param bound a negative value specifies no bound
     * @param depth a negative value specifies no bound
     * @return
     */
    public List<ConstrainedTerm> search(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules,
            int bound,
            int depth) {
        stopwatch.start();

        List<ConstrainedTerm> searchResults = new ArrayList<ConstrainedTerm>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();
        List<ConstrainedTerm> queue = new ArrayList<ConstrainedTerm>();
        List<ConstrainedTerm> nextQueue = new ArrayList<ConstrainedTerm>();

        visited.add(initialTerm);
        queue.add(initialTerm);

    label:
        for (step = 0; !queue.isEmpty() && step != depth; ++step) {
            for (ConstrainedTerm term : queue) {
                computeRewriteStep(term);

                if (results.isEmpty()) {
                    /* final term */
                    searchResults.add(term);
                    if (searchResults.size() == bound) {
                        break label;
                    }

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
        }

        /* add the configurations on the depth frontier */
        while (!queue.isEmpty() && searchResults.size() != bound) {
            searchResults.add(queue.remove(0));
        }

        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");

        return searchResults;
    }

    public List<ConstrainedTerm> prove(List<Rule> rules, FileSystem fs) {
        stopwatch.start();

        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();
        for (Rule rule : rules) {
            /* rename rule variables */
            Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.variableSet());

            TermContext context = new TermContext(definition, fs);
            SymbolicConstraint sideConstraint = new SymbolicConstraint(context);
            sideConstraint.addAll(rule.condition());
            ConstrainedTerm initialTerm = new ConstrainedTerm(
                    rule.leftHandSide().substitute(freshSubstitution, context),
                    rule.lookups().getSymbolicConstraint(context).substitute(
                            freshSubstitution,
                            context),
                    sideConstraint.substitute(freshSubstitution, context),
                    context);

            ConstrainedTerm targetTerm = new ConstrainedTerm(
                    rule.rightHandSide().substitute(freshSubstitution, context),
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

        visited.add(initialTerm);
        queue.add(initialTerm);
        boolean guarded = false;
        while (!queue.isEmpty()) {
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

}

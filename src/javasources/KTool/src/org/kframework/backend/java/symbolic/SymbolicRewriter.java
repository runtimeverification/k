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
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.strategies.TransitionCompositeStrategy;
import org.kframework.backend.java.util.ProductionsOfSort;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.api.SearchType;
import org.kframework.utils.general.GlobalSettings;

import java.util.Collection;
import java.util.ArrayList;
import java.util.HashMap;
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
    private final TransitionCompositeStrategy strategy
        = new TransitionCompositeStrategy(GlobalSettings.transition);
    private final Stopwatch stopwatch = new Stopwatch();
    private int step;
    private final Stopwatch ruleStopwatch = new Stopwatch();
    private final Map<Index, Set<Rule>> ruleTable;
    private final Map<Index, Set<Rule>> heatingRuleTable;
    private final Map<Index, Set<Rule>> coolingRuleTable;
    private final Set<Rule> unindexedRules;
    private final List<ConstrainedTerm> results = new ArrayList<ConstrainedTerm>();
    private boolean transition;

	public SymbolicRewriter(Definition definition) {
        this.definition = definition;
        
        /* computes the map from sorts to production terms */
        ProductionsOfSort.init(definition);
//        System.out.println(ProductionsOfSort.getProdTermsOf("AExp"));
        
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

        /* Map each index to a set of rules unifiable with that index */
        /* Heating rules and regular rules have their first index checked */
        /* Cooling rules have their second index checked */
        ImmutableMap.Builder<Index, Set<Rule>> mapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, Set<Rule>> heatingMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, Set<Rule>> coolingMapBuilder = ImmutableMap.builder();
        for (Index index : indices) {
          ImmutableSet.Builder<Rule> setBuilder = ImmutableSet.builder();
          ImmutableSet.Builder<Rule> heatingSetBuilder = ImmutableSet.builder();
          ImmutableSet.Builder<Rule> coolingSetBuilder = ImmutableSet.builder();
          for (Rule rule : definition.rules()) {
            if (rule.containsAttribute("heat")) {
              if (index.isUnifiable(rule.indexingPair().first)) {
                heatingSetBuilder.add(rule);
              }
            } else if (rule.containsAttribute("cool")) {
              if (index.isUnifiable(rule.indexingPair().second)) {
                coolingSetBuilder.add(rule);
              }
            } else {
              if (index.isUnifiable(rule.indexingPair().first)) {
                setBuilder.add(rule);
              }
            }
          }
          ImmutableSet<Rule> rules = setBuilder.build();
          if (!rules.isEmpty()) {
            mapBuilder.put(index, rules);
          }
          rules = heatingSetBuilder.build();
          if (!rules.isEmpty()) {
            heatingMapBuilder.put(index, rules);
          }
          rules = coolingSetBuilder.build();
          if (!rules.isEmpty()) {
            coolingMapBuilder.put(index, rules);
          }
        }
        heatingRuleTable = heatingMapBuilder.build();
        coolingRuleTable = coolingMapBuilder.build();
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
            if (ruleTable.get(pair.first) != null) {
                rules.addAll(ruleTable.get(pair.first));
            }
            if (heatingRuleTable.get(pair.first) != null) {
                rules.addAll(heatingRuleTable.get(pair.first));
            }
            if (coolingRuleTable.get(pair.second) != null) {
                rules.addAll(coolingRuleTable.get(pair.second));
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

        // Applying a strategy to a set of rules divides the rules up into
        // equivalence classes of rules. We iterate through these equivalence
        // classes one at a time, seeing which one contains rules we can apply.
//        System.out.println(LookupCell.find(constrainedTerm.term(),"k"));
        strategy.reset(getRules(constrainedTerm.term()));
        while (strategy.hasNext()) {
            transition = strategy.nextIsTransition();
            Collection<Rule> rules = strategy.next();
            for (Rule rule : rules) {
                ruleStopwatch.reset();
                ruleStopwatch.start();

                SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(
                        constrainedTerm.termContext());
                leftHandSideConstraint.addAll(rule.requires());
                for (Variable variable : rule.freshVariables()) {
                    leftHandSideConstraint.add(variable, IntToken.fresh());
                }

                ConstrainedTerm leftHandSide = new ConstrainedTerm(
                        rule.leftHandSide(),
                        rule.lookups().getSymbolicConstraint(constrainedTerm.termContext()),
                        leftHandSideConstraint,
                        constrainedTerm.termContext());

                for (SymbolicConstraint constraint1 : constrainedTerm.unify(leftHandSide)) {
                    constraint1.orientSubstitution(rule.variableSet(), constrainedTerm.termContext());
                    constraint1.addAll(rule.ensures());
                    /* rename rule variables in the constraints */
                    Map<Variable, Variable> freshSubstitution = constraint1.rename(rule.variableSet());

                    Term result = rule.rightHandSide();
                    /* rename rule variables in the rule RHS */
                    result = result.substituteWithBinders(freshSubstitution, constrainedTerm.termContext());
                    /* apply the constraints substitution on the rule RHS */
                    result = result.substituteAndEvaluate(constraint1.substitution(),
                            constrainedTerm.termContext());
                    /* evaluate pending functions in the rule RHS */
//                    result = result.evaluate(constrainedTerm.termContext());
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
            // If we've found matching results from one equivalence class then
            // we are done, as we can't match rules from two equivalence classes
            // in the same step.
            if (results.size() > 0) {
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
            constraint.addAll(rule.ensures());

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
            constraint.eliminateAnonymousVariables();

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
            termConstraint.add(var, IntToken.fresh());
        }

        // Create a constrained term from the left hand side of the pattern.
        ConstrainedTerm lhs = new ConstrainedTerm(
                pattern.leftHandSide(),
                pattern.lookups().getSymbolicConstraint(term.termContext()),
                termConstraint,
                term.termContext());

        // Collect the variables we are interested in finding
        VariableVisitor visitor = new VariableVisitor();
        lhs.accept(visitor);

        Collection<SymbolicConstraint> constraints = term.unify(lhs);
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
            constraint.orientSubstitution(visitor.getVariableSet(), term.termContext());
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

        // The search queues will map terms to their depth in terms of transitions.
        Map<ConstrainedTerm,Integer> queue = new HashMap<ConstrainedTerm,Integer>();
        Map<ConstrainedTerm,Integer> nextQueue = new HashMap<ConstrainedTerm,Integer>();

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
    
    /**
    *
    * @param initialTerm
    * @param targetTerm not implemented yet
    * @param rules not implemented yet
    * @param bound a negative value specifies no bound
    * @param depth a negative value specifies no bound
    * @return
    */
    public List<ConstrainedTerm> generate(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules,
            int bound,
            int depth) {
        stopwatch.start();

        List<ConstrainedTerm> testgenResults = new ArrayList<ConstrainedTerm>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();
        List<ConstrainedTerm> queue = new ArrayList<ConstrainedTerm>();
        List<ConstrainedTerm> nextQueue = new ArrayList<ConstrainedTerm>();

        visited.add(initialTerm);
        queue.add(initialTerm);

    label:
        for (step = 0; !queue.isEmpty() && step != depth; ++step) {
            for (ConstrainedTerm term : queue) {
                // TODO(YilongL): handle the following pruning condition nice and clean
                if (term.variableSet().size() > 10) continue;
                
                computeRewriteStep(term);

                if (results.isEmpty()) {
                    /* final term */
                    testgenResults.add(term);
                    if (testgenResults.size() == bound) {
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
//            queue = TestCaseGenerationUtil.getArbitraryStates(nextQueue, 30);
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        /* add the configurations on the depth frontier */
        while (!queue.isEmpty() && testgenResults.size() != bound) {
            ConstrainedTerm cnstrTerm = queue.remove(0);
            computeRewriteStep(cnstrTerm, 1);
            if (results.isEmpty())
                testgenResults.add(cnstrTerm);
        }

        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + step + "steps, " + stopwatch + "]");

        return testgenResults;
    }    

    public List<ConstrainedTerm> prove(List<Rule> rules, FileSystem fs) {
        stopwatch.start();

        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();
        for (Rule rule : rules) {
            /* rename rule variables */
            Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.variableSet());

            TermContext context = new TermContext(definition, fs);
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

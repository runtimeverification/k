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
import org.kframework.backend.java.kil.ConstrainedTerm;import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.Attributes;

import java.util.ArrayList;
import java.util.Collections;
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
    private final Stopwatch stopwatch = new Stopwatch();
    private final Stopwatch ruleStopwatch = new Stopwatch();
    private final Map<IndexingPair, Set<Rule>> ruleTable;
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
	}

    public ConstrainedTerm rewrite(ConstrainedTerm constrainedTerm, int bound) {
        stopwatch.start();

        for (int i = 0; i != bound; ++i) {
            /* get the first solution */
            computeRewriteStep(constrainedTerm);
            ConstrainedTerm result = getTransition(0);
            if (result != null) {
                constrainedTerm = result;
            } else {
                break;
            }
        }

        stopwatch.stop();
        System.err.println("[" + stopwatch +"]");

        return constrainedTerm;
    }

    public ConstrainedTerm rewrite(ConstrainedTerm constrainedTerm) {
        return rewrite(constrainedTerm, -1);
    }

    private Set<Rule> getRules(Term term) {
        final List<Term> contents = new ArrayList<Term>();
        term.accept(new BottomUpVisitor() {
            @Override
            public void visit(Cell cell) {
                if (cell.contentKind() == Kind.CELL_COLLECTION) {
                    super.visit(cell);
                } else if (cell.getLabel().equals("k")) {
                    contents.add(cell.getContent());
                }
            }
        });

        Set<Rule> rules = new HashSet<Rule>();
        for (Term content : contents) {
            IndexingPair pair = IndexingPair.getIndexingPair(content);
            if (ruleTable.get(pair) != null) {
                rules.addAll(ruleTable.get(pair));
            }
        }

        return rules;
    }

    private ConstrainedTerm getTransition(int n) {
        return n < results.size() ? results.get(n) : null;
    }

    private void computeRewriteStep(ConstrainedTerm constrainedTerm) {
        results.clear();

        for (Rule rule : getRules(constrainedTerm.term())) {
            ruleStopwatch.reset();
            ruleStopwatch.start();

            SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(definition);
            leftHandSideConstraint.addAll(rule.condition());
            for (Variable variable : rule.freshVariables()) {
                leftHandSideConstraint.add(variable, IntToken.fresh());
            }

            ConstrainedTerm leftHandSide = new ConstrainedTerm(
                    rule.leftHandSide(),
                    rule.lookups(),
                    leftHandSideConstraint);

            for (SymbolicConstraint constraint1 : constrainedTerm.unify(leftHandSide, definition)) {
                /* rename rule variables in the constraints */
                Map<Variable, Variable> freshSubstitution = constraint1.rename(rule.variableSet());

                Term result = rule.rightHandSide();
                /* rename rule variables in the rule RHS */
                result = result.substitute(freshSubstitution, definition);
                /* apply the constraints substitution on the rule RHS */
                result = result.substitute(constraint1.substitution(), definition);
                /* evaluate pending functions in the rule RHS */
                result = result.evaluate(definition);
                /* eliminate anonymous variables */
                constraint1.eliminateAnonymousVariables();

                /*
                System.err.println("rule \n\t" + rule);
                System.err.println("result constraint\n\t" + constraint1);
                System.err.println("result term\n\t" + result);
                System.err.println("============================================================"); */

                //ruleStopwatch.stop();
                //System.err.println("### " + ruleStopwatch);


                /* compute all results */
                results.add(new ConstrainedTerm(result, constraint1, definition));
            }
        }
        //System.out.println("Result: " + results.toString());
    }

    /**
     * Apply a specification rule
     */
    private ConstrainedTerm applyRule(ConstrainedTerm constrainedTerm, List<Rule> rules) {
        for (Rule rule : rules) {
            ruleStopwatch.reset();
            ruleStopwatch.start();

            SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(definition);
            leftHandSideConstraint.addAll(rule.condition());

            ConstrainedTerm leftHandSideTerm = new ConstrainedTerm(
                    rule.leftHandSide(),
                    rule.lookups(),
                    leftHandSideConstraint);

            SymbolicConstraint constraint = constrainedTerm.match(leftHandSideTerm, definition);
            if (constraint == null) {
                continue;
            }

            /* rename rule variables in the constraints */
            Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());

            Term result = rule.rightHandSide();
            /* rename rule variables in the rule RHS */
            result = result.substitute(freshSubstitution, definition);
            /* apply the constraints substitution on the rule RHS */
            result = result.substitute(constraint.substitution(), definition);
            /* evaluate pending functions in the rule RHS */
            result = result.evaluate(definition);
            /* eliminate anonymous variables */
            constraint.eliminateAnonymousVariables();

            /* return first solution */
            return new ConstrainedTerm(result, constraint, definition);
        }

        return null;
    }

    /*
    Search with neither bound nor depth specified
     */
    public List<ConstrainedTerm> search(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules) {
        stopwatch.start();

        List<ConstrainedTerm> searchResults = new ArrayList<ConstrainedTerm>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();
        List<ConstrainedTerm> queue = new ArrayList<ConstrainedTerm>();
        List<ConstrainedTerm> nextQueue = new ArrayList<ConstrainedTerm>();

        visited.add(initialTerm);
        queue.add(initialTerm);
        while (!queue.isEmpty()) {
            for (ConstrainedTerm term : queue) {
                computeRewriteStep(term);

                if (results.isEmpty()) {
                    /* final term */
                    searchResults.add(term);
                }


                for (int i = 0; getTransition(i) != null; ++i) {
                    if (visited.add(getTransition(i))) {
                        nextQueue.add(getTransition(i));
                    }
                }
            }

            /* swap the queues */
            ListPair swappedPair = swapQueues(new ListPair(queue,nextQueue));
            queue = swappedPair.getQ1();
            nextQueue = swappedPair.getQ2();

            /*
            for (ConstrainedTerm result : queue) {
                System.err.println(result);
            }
            System.err.println("============================================================");
            */
        }




        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + stopwatch +"]");

        return searchResults;
    }

    /*
    Search with only bound specified
     */
    public List<ConstrainedTerm> search(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules, Integer bound) {

        if (bound == null) {
            return search(initialTerm,targetTerm,rules);
        }

        stopwatch.start();

        List<ConstrainedTerm> searchResults = new ArrayList<ConstrainedTerm>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();
        List<ConstrainedTerm> queue = new ArrayList<ConstrainedTerm>();
        List<ConstrainedTerm> nextQueue = new ArrayList<ConstrainedTerm>();

        visited.add(initialTerm);
        queue.add(initialTerm);

        while (!queue.isEmpty()) {

            for (ConstrainedTerm term : queue) {
                computeRewriteStep(term);

                if (results.isEmpty()) {
                    if (searchResults.size() < bound){
                        /* final term */
                        searchResults.add(term);
                    } else{
                        return searchResults;
                    }

                }

                for (int i = 0; getTransition(i) != null; ++i) {
                    if (visited.add(getTransition(i))) {
                        nextQueue.add(getTransition(i));
                    }
                }
            }

            /* swap the queues */
            ListPair swappedPair = swapQueues(new ListPair(queue,nextQueue));
            queue = swappedPair.getQ1();
            nextQueue = swappedPair.getQ2();

            /*
            for (ConstrainedTerm result : queue) {
                System.err.println(result);
            }
            System.err.println("============================================================");
            */
        }

        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + stopwatch +"]");

        return searchResults;
    }

    /*
    Search with all bound and depth.
     */
    public List<ConstrainedTerm> search(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules, Integer bound, Integer depth) {
        int count = 0;

        /*Check if which of "bound" or "depth" is specified
        * by the user*/
        if (bound == null & depth == null) {
            return search(initialTerm,targetTerm,rules);
        }else if (bound!=null & depth==null){
            return search(initialTerm,targetTerm,rules,bound);
        } else if (bound == null & depth !=null){
            //TO DO: handle this "properly"
           throw new UnsupportedOperationException("-depth flag is set but the -bound flag is not");
        }

        stopwatch.start();


        List<ConstrainedTerm> searchResults = new ArrayList<ConstrainedTerm>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();
        List<ConstrainedTerm> queue = new ArrayList<ConstrainedTerm>();
        List<ConstrainedTerm> nextQueue = new ArrayList<ConstrainedTerm>();

        visited.add(initialTerm);
        queue.add(initialTerm);

        label: while (!queue.isEmpty() && count < depth) {
            for (ConstrainedTerm term : queue) {
                computeRewriteStep(term);

                if (results.isEmpty()) {

                    if (searchResults.size() < bound){
                        /* final term */
                        searchResults.add(term);
                    } else{
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
            ListPair swappedPair = swapQueues(new ListPair(queue,nextQueue));
            queue = swappedPair.getQ1();
            nextQueue = swappedPair.getQ2();
            count+=1;

            /*
            for (ConstrainedTerm result : queue) {
                System.err.println(result);
            }
            System.err.println("============================================================");
            */
        }


        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + stopwatch +"]");

        return searchResults;
    }

    /*
    Search with all bound and depth.
     */
    public List<ConstrainedTerm> search(
            ConstrainedTerm initialTerm,
            ConstrainedTerm targetTerm,
            List<Rule> rules, Integer bound, Integer depth, boolean boundConstrained) {
        int count = 0;

        /*Check if which of "bound" or "depth" is specified
        * by the user*/
        if (bound == null & depth == null) {
            return search(initialTerm,targetTerm,rules);
        }else if (bound!=null & depth==null){
            return search(initialTerm,targetTerm,rules,bound);
        } else if (bound == null & depth !=null){
            //TO DO: handle this "properly"
            throw new UnsupportedOperationException("-depth flag is set but the -bound flag is not");
        }

        stopwatch.start();


        List<ConstrainedTerm> searchResults = new ArrayList<ConstrainedTerm>();
        Set<ConstrainedTerm> visited = new HashSet<ConstrainedTerm>();
        List<ConstrainedTerm> queue = new ArrayList<ConstrainedTerm>();
        List<ConstrainedTerm> nextQueue = new ArrayList<ConstrainedTerm>();

        visited.add(initialTerm);
        queue.add(initialTerm);

        label: while (!queue.isEmpty() && count < depth) {
            for (ConstrainedTerm term : queue) {
                computeRewriteStep(term);

                if (results.isEmpty()) {

                    if (searchResults.size() < bound){
                        /* final term */
                        searchResults.add(term);
                    } else{
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
            ListPair swappedPair = swapQueues(new ListPair(queue,nextQueue));
            queue = swappedPair.getQ1();
            nextQueue = swappedPair.getQ2();
            count+=1;
            /*
            for (ConstrainedTerm result : queue) {
                System.err.println(result);
            }
            System.err.println("============================================================");
            */
        }

        if(boundConstrained){
           searchResults.addAll(queue);
        }


        stopwatch.stop();
        System.err.println("[" + visited.size() + "states, " + stopwatch +"]");

        return searchResults;
    }

    private ListPair swapQueues(ListPair pair){
        List<ConstrainedTerm> temp;
        temp = pair.getQ1();
        pair.setQ1(pair.getQ2());
        pair.setQ2(temp); //why assign temp to nextQueue if it will eventually be cleared. Possible optimization?
        pair.getQ2().clear();
        return pair;
    }

    /*
    Used for holding pairs to be swapped. Looks like lots of code to do such a simple thing.
    Owolabi: revert to andrei's swap
     */
    private class ListPair{
        private List<ConstrainedTerm> q1,q2;
        ListPair(List<ConstrainedTerm> queue1, List<ConstrainedTerm> queue2){
            this.q1 = queue1;
            this.q2 = queue2;
        }

        List<ConstrainedTerm> getQ1(){
            return this.q1;
        }

        void setQ1(List<ConstrainedTerm> q){
            this.q1 = q;
        }

        List<ConstrainedTerm> getQ2(){
            return this.q2;
        }

        void setQ2(List<ConstrainedTerm> q){
            this.q2 = q;
        }
    }

    public List<ConstrainedTerm> prove(List<Rule> rules) {
        stopwatch.start();

        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();
        for (Rule rule : rules) {
            /* rename rule variables */
            Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(rule.variableSet());

            SymbolicConstraint sideConstraint = new SymbolicConstraint(definition);
            sideConstraint.addAll(rule.condition());
            ConstrainedTerm initialTerm = new ConstrainedTerm(
                    rule.leftHandSide().substitute(freshSubstitution, definition),
                    rule.lookups().substitute(freshSubstitution, definition),
                    sideConstraint.substitute(freshSubstitution, definition));

            ConstrainedTerm targetTerm = new ConstrainedTerm(
                    rule.rightHandSide().substitute(freshSubstitution, definition),
                    definition);

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
                if (term.implies(targetTerm, definition)) {
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

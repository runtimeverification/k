package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import com.google.common.base.Stopwatch;


/**
 * @author AndreiS
 */
public class StepRewriter {

    private final Definition definition;
    private final Collection<Rule> rules;
    private final Stopwatch stopwatch = new Stopwatch();
    private Collection<ConstrainedTerm> constrainedTermResults = new ArrayList<ConstrainedTerm>();
    private Collection<Term> termResults = new ArrayList<Term>();

    public StepRewriter(Collection<Rule> rules, Definition definition) {
        this.rules = new ArrayList<Rule>(rules);
        this.definition = definition;
    }

    public Collection<Term> getAllSuccessors(Term term) {
        for (Rule rule : rules) {
            rewriteByRule(term, rule);
        }
        return termResults;
    }

    public Collection<ConstrainedTerm> getAllNarrowingSuccessors(ConstrainedTerm constrainedTerm) {
        for (Rule rule : rules) {
            narrowByRule(constrainedTerm, rule);
        }
        return constrainedTermResults;
    }

    public Term getOneSuccessor(Term term) {
        for (Rule rule : rules) {
            rewriteByRule(term, rule);
            if (!termResults.isEmpty()) {
                return termResults.iterator().next();
            }
        }
        return null;
    }

    public ConstrainedTerm getOneNarrowingSuccessor(ConstrainedTerm constrainedTerm) {
        for (Rule rule : rules) {
            narrowByRule(constrainedTerm, rule);
            if (!constrainedTermResults.isEmpty()) {
                return constrainedTermResults.iterator().next();
            }
        }
        return null;
    }

    private void narrowByRule(ConstrainedTerm constrainedTerm, Rule rule) {
        stopwatch.reset();
        stopwatch.start();

        constrainedTermResults = new ArrayList<ConstrainedTerm>();

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

        for (SymbolicConstraint constraint : constrainedTerm.unify(leftHandSide)) {
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

            /* compute all results */
            constrainedTermResults.add(new ConstrainedTerm(result, constraint,
                constrainedTerm.termContext()));
        }

        stopwatch.stop();
    }

    // apply rule by matching
    private void rewriteByRule(Term term, Rule rule) {
        stopwatch.reset();
        stopwatch.start();

        termResults = new ArrayList<Term>();

        TermContext context = new TermContext(definition);
        ConstrainedTerm constrainedTerm = new ConstrainedTerm(term, context);

        SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(context);
        leftHandSideConstraint.addAll(rule.requires());
        for (Variable variable : rule.freshVariables()) {
            leftHandSideConstraint.add(variable, IntToken.fresh());
        }

        ConstrainedTerm leftHandSide = new ConstrainedTerm(
                rule.leftHandSide(),
                rule.lookups().getSymbolicConstraint(context),
                leftHandSideConstraint,
                context);

        for (SymbolicConstraint constraint : constrainedTerm.unify(leftHandSide)) {
            /* check the constraint represents a match */
            if (!constraint.isSubstitution()
                    || !constraint.substitution().keySet().equals(rule.variableSet())) {
                continue;
            }

            Term result = rule.rightHandSide();
            /* apply the constraints substitution on the rule RHS */
            result = result.substituteWithBinders(constraint.substitution(), context);
            /* evaluate pending functions in the rule RHS */
            result = result.evaluate(context);

            /* compute all results */
            termResults.add(result);
        }

        stopwatch.stop();
    }

}

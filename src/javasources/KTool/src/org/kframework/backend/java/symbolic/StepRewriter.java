// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

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
    private GlobalContext globalContext;

    public StepRewriter(Collection<Rule> rules, Definition definition) {
        this.rules = new ArrayList<Rule>(rules);
        this.definition = definition;
        this.globalContext = new GlobalContext(definition, null);
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
            leftHandSideConstraint.add(
                    variable,
                    FreshOperations.fresh(variable.sort(), constrainedTerm.termContext()));
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

        TermContext context = TermContext.of(globalContext);
        ConstrainedTerm constrainedTerm = new ConstrainedTerm(term, context);

        SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(context);
        leftHandSideConstraint.addAll(rule.requires());
        for (Variable variable : rule.freshVariables()) {
            leftHandSideConstraint.add(variable, FreshOperations.fresh(variable.sort(), context));
        }

        ConstrainedTerm leftHandSide = new ConstrainedTerm(
                rule.leftHandSide(),
                rule.lookups().getSymbolicConstraint(context),
                leftHandSideConstraint,
                context);

        for (SymbolicConstraint constraint : constrainedTerm.unify(leftHandSide)) {
            if (!constraint.isMatching(leftHandSide)) {
                continue;
            }

            constraint.orientSubstitution(leftHandSide.variableSet());

            Term result = rule.rightHandSide();
            /* apply the constraints substitution on the rule RHS */
            result = result.substituteAndEvaluate(constraint.substitution(), context);

            /* compute all results */
            termResults.add(result);
        }

        stopwatch.stop();
    }

}

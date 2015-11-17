// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.Sets;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.rewritemachine.RHSInstruction;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Equality;
import org.kframework.backend.java.symbolic.ImmutableMapSubstitution;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.RuleAuditing;
import org.kframework.backend.java.symbolic.Substitution;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Utilities for the Java rewrite engine.
 *
 * @author YilongL
 */
public class RewriteEngineUtils {

    public static boolean isSubsortedEq(Term big, Term small, Definition definition) {
        return definition.subsorts().isSubsortedEq(big.sort(), small.sort());
    }

    /**
     * Evaluates the side-conditions of a rule according to a given
     * substitution and updates the substitution accordingly.
     *
     * @return the updated substitution if it satisfies the side-condition;
     *         otherwise, {@code null}
     */
    public static Substitution<Variable, Term> evaluateConditions(
            Rule rule,
            Substitution<Variable, Term> substitution,
            TermContext context) {
        /* handle fresh variables, data structure lookups, and side conditions */

        Substitution<Variable, Term> crntSubst = substitution;
        /* add bindings for fresh variables used in the rule */
        for (Variable variable : rule.freshConstants()) {
            crntSubst = crntSubst.plus(variable, FreshOperations.freshOfSort(variable.sort(), context));
        }

        /* evaluate data structure lookups/choices and add bindings for them */
        Profiler.startTimer(Profiler.EVALUATE_LOOKUP_CHOICE_TIMER);
        int i = 0;
        for (Equality equality : rule.lookups().equalities()) {
            Term lookupOrChoice = equality.leftHandSide();
            Term nonLookupOrChoice =  equality.rightHandSide();
            List<RHSInstruction> instructions = rule.instructionsOfLookups().get(i);
            Term evalLookupOrChoice = KAbstractRewriteMachine.construct(instructions, crntSubst, null, context, false);

            boolean resolved = false;
            if (evalLookupOrChoice instanceof Bottom
                    || DataStructures.isLookupOrChoice(evalLookupOrChoice)) {
                /* the data-structure lookup or choice operation is either undefined or pending due to symbolic argument(s) */

                // when the operation is pending, it is not really a valid match
                // for example, matching ``<env>... X |-> V ...</env>''
                // against ``<env> Rho </env>'' will result in a pending
                // choice operation due to the unknown ``Rho''.

                if (RuleAuditing.isAuditBegun()) {
                    System.err.println("Matching failure: unable to resolve collection operation "
                    + lookupOrChoice.substitute(crntSubst) + "; evaluated to "
                    + evalLookupOrChoice);
                }
            } else {
                if (nonLookupOrChoice instanceof Variable) {
                    Variable variable = (Variable) nonLookupOrChoice;
                    if (context.definition().subsorts().isSubsortedEq(variable.sort(), evalLookupOrChoice.sort())) {
                        Substitution<Variable, Term> newSubst = crntSubst.plus(variable, evalLookupOrChoice);
                        resolved = newSubst != null;
                        if (!resolved && RuleAuditing.isAuditBegun()) {
                            System.err.println("Matching failure: " + variable + " must match both "
                            + crntSubst.get(variable) + " and " + evalLookupOrChoice);
                        }
                        crntSubst = newSubst;
                    }
                } else {
                    // the non-lookup term is not a variable and thus requires further pattern matching
                    // for example: L:List[Int(#"0")] = '#ostream(_)(I:Int), where L is the output buffer
                    //           => '#ostream(_)(Int(#"1")) =? '#ostream(_)(I:Int)

                    Term evalNonLookupOrChoice = nonLookupOrChoice.substituteAndEvaluate(crntSubst, context);

                    PatternMatcher lookupMatcher = new PatternMatcher(rule.isLemma(), true, context);
                    if (lookupMatcher.patternMatch(evalLookupOrChoice, evalNonLookupOrChoice)) {
                        if (nonLookupOrChoice.variableSet().containsAll(lookupMatcher.substitution().keySet())) {
                            resolved = true;
                            crntSubst = crntSubst.plusAll(lookupMatcher.substitution());
                        } else if (RuleAuditing.isAuditBegun()) {
                            System.err.println("Matching failure: substitution "
                            + lookupMatcher.substitution() + " missing variables "
                            + Sets.difference(lookupMatcher.substitution().keySet(), nonLookupOrChoice.variableSet()));
                        }
                    }
                }
            }

            if (!resolved) {
                crntSubst = null;
                break;
            }
            ++i;
        }
        Profiler.stopTimer(Profiler.EVALUATE_LOOKUP_CHOICE_TIMER);


        /* evaluate side conditions */
        Profiler.startTimer(Profiler.EVALUATE_REQUIRES_TIMER);
        if (crntSubst != null) {
            i = 0;
            for (Term require : rule.requires()) {
                // TODO(YilongL): in the future, we may have to accumulate
                // the substitution obtained from evaluating the side
                // condition
                Term evaluatedReq = KAbstractRewriteMachine.construct(rule.instructionsOfRequires().get(i), crntSubst, null, context, false);
                if (!evaluatedReq.equals(BoolToken.TRUE)) {
                    if (!evaluatedReq.isGround()
                            && context.getTopConstraint() != null
                            && context.getTopConstraint().implies(ConjunctiveFormula.of(context.global()).add(evaluatedReq, BoolToken.TRUE), Collections.emptySet())) {
                        i++;
                        continue;
                    }
                    if (RuleAuditing.isAuditBegun()) {
                        System.err.println("Side condition failure: " + require.substituteWithBinders(crntSubst) + " evaluated to " + evaluatedReq);
                    }
                    crntSubst = null;
                    break;
                }
                i++;
            }
        }
        Profiler.stopTimer(Profiler.EVALUATE_REQUIRES_TIMER);

        return crntSubst;
    }

    /**
     * Evaluates the side-conditions of a rule against a list of possible
     * instantiations.
     *
     * @return a list of instantiations that satisfy the side-conditions; each
     *         of which is updated with extra bindings introduced during the
     *         evaluation
     */
    public static List<Substitution<Variable, Term>> evaluateConditions(
            Rule rule,
            List<Substitution<Variable, Term>> substitutions,
            TermContext context) {
        /* handle fresh variables, data structure lookups, and side conditions */
        return substitutions.stream()
                .map(s -> evaluateConditions(rule, ImmutableMapSubstitution.from(s), context))
                .filter(s -> s != null)
                .collect(Collectors.toList());
    }

}

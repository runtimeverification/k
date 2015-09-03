// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.rewritemachine.RHSInstruction;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Equality;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.Substitution;
import org.kframework.backend.java.symbolic.RuleAuditing;

import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

/**
 * Utilities for the Java rewrite engine.
 *
 * @author YilongL
 */
public class RewriteEngineUtils {

    public static boolean isSubsorted(Term big, Term small, TermContext context) {
        return context.definition().subsorts().isSubsorted(big.sort(), small.sort());
    }

    public static boolean isSubsortedEq(Term big, Term small, TermContext context) {
        return context.definition().subsorts().isSubsortedEq(big.sort(), small.sort());
    }

    /**
     * Evaluates the side-conditions of a rule according to a given
     * substitution and updates the substitution accordingly.
     *
     * @param rule
     * @param substitution
     * @param context
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

                if (!resolved && RuleAuditing.isAuditBegun()) {
                    System.err.println("Matching failure: unable to resolve collection operation "
                    + lookupOrChoice.substitute(crntSubst, context) + "; evaluated to "
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
                        } else if (!resolved && RuleAuditing.isAuditBegun()) {
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
                            && context.getTopConstraint().implies(ConjunctiveFormula.of(context).add(evaluatedReq, BoolToken.TRUE), Collections.emptySet())) {
                        i++;
                        continue;
                    }
                    if (RuleAuditing.isAuditBegun()) {
                        System.err.println("Side condition failure: " + require.substituteWithBinders(crntSubst, context) + " evaluated to " + evaluatedReq);
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
     * @param rule
     * @param substitutions
     * @param context
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
                .map(s -> evaluateConditions(rule, Substitution.from(s), context))
                .filter(s -> s != null)
                .collect(Collectors.toList());
    }

    public static Term evaluateLookupOrChoice(Term lookupOrChoice, Map<Variable, Term> subst, TermContext context) {
        Term evalLookupOrChoice = lookupOrChoice.copyOnShareSubstAndEval(subst, context);
        return evalLookupOrChoice;
    }

    /**
     * Helper method which constructs all possible variable bindings of
     * the pattern term to match the subject term.
     *
     * @return all possible substitutions of the pattern term to match the
     *         subject term
     */
    public static List<Map<Variable, Term>> getMultiSubstitutions(
            Map<Variable, Term> fSubstitution,
            Collection<Collection<Map<Variable, Term>>> multiSubstitutions) {
        if (!multiSubstitutions.isEmpty()) {
            assert multiSubstitutions.size() <= 2;

            List<Map<Variable, Term>> result = new ArrayList<Map<Variable, Term>>();
            Iterator<Collection<Map<Variable, Term>>> iterator = multiSubstitutions.iterator();
            if (multiSubstitutions.size() == 1) {
                for (Map<Variable, Term> subst : iterator.next()) {
                    Map<Variable, Term> composedSubst = composeSubstitution(fSubstitution, subst);
                    if (composedSubst != null) {
                        result.add(composedSubst);
                    }
                }
            } else {
                Collection<Map<Variable, Term>> substitutions = iterator.next();
                Collection<Map<Variable, Term>> otherSubstitutions = iterator.next();
                for (Map<Variable, Term> subst1 : substitutions) {
                    for (Map<Variable, Term> subst2 : otherSubstitutions) {
                        Map<Variable, Term> composedSubst = composeSubstitution(fSubstitution, subst1);
                        if (composedSubst != null) {
                            // TODO(YilongL): might be able to exploit the fact that composedSubst can be safely mutated
                            composedSubst = composeSubstitution(composedSubst, subst2);
                            if (composedSubst != null) {
                                result.add(composedSubst);
                            }
                        }
                    }
                }
            }
            return result;
        } else {
            Map<Variable, Term> substitution = Maps.newHashMap(fSubstitution);
            return Collections.singletonList(substitution);
        }
    }

    /**
     * Composes two specified substitutions.
     *
     * @param subst1
     *            the first substitution
     * @param subst2
     *            the second substitution
     * @return the composed substitution on success; otherwise, {@code null}
     */
    public static Map<Variable, Term> composeSubstitution(Map<Variable, Term> subst1, Map<Variable, Term> subst2) {
        if (subst1.size() < subst2.size()) {
            Map<Variable, Term> tmp = subst1;
            subst1 = subst2;
            subst2 = tmp;
        }

        Map<Variable, Term> result = new HashMap<>(subst1);
        for (Map.Entry<Variable, Term> entry : subst2.entrySet()) {
            Variable variable = entry.getKey();
            Term term = entry.getValue();
            Term otherTerm = result.get(variable);
            if (otherTerm == null) {
                result.put(variable, term);
            } else if (!otherTerm.equals(term)) {
                if (RuleAuditing.isAuditBegun()) {
                    System.err.println("Incompatible substitutions: " + subst1 + " and " + subst2);
                }
                return null;
            }
        }
        return result;
    }

    /**
     * Composes a list of substitutions.
     *
     * @param substs
     *            a list of substitutions
     * @return the composed substitution on success; otherwise, {@code null}
     */
    @SafeVarargs
    public static Map<Variable, Term> composeSubstitution(Map<Variable, Term>... substs) {
        switch (substs.length) {
        case 0:
            return null;

        case 1:
            return substs[0];

        case 2:
            return composeSubstitution(substs[0], substs[1]);

        default:
            Map<Variable, Term> subst = substs[0];
            for (int idx = 1; idx < substs.length; idx++) {
                subst = composeSubstitution(subst, substs[idx]);
            }
            return subst;
        }
    }

}

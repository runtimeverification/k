// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.UninterpretedConstraint;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

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
    public static Map<Variable, Term> evaluateConditions(Rule rule, Map<Variable, Term> substitution,
            TermContext context) {
        /* handle fresh variables, data structure lookups, and side conditions */

        Map<Variable, Term> crntSubst = substitution;
        /* add bindings for fresh variables used in the rule */
        for (Variable variable : rule.freshConstants()) {
            crntSubst.put(variable, FreshOperations.fresh(variable.sort(), context));
        }

        /* evaluate data structure lookups/choices and add bindings for them */
        for (UninterpretedConstraint.Equality equality : rule.lookups().equalities()) {
            Term lookupOrChoice = equality.leftHandSide();
            Term nonLookupOrChoice =  equality.rightHandSide();

                    Term evalLookupOrChoice = evaluateLookupOrChoice(lookupOrChoice, crntSubst, context);

                    boolean resolved = false;
                    if (evalLookupOrChoice == null || evalLookupOrChoice instanceof Bottom) {
                        /* the data-structure lookup or choice operation is either undefined or pending due to symbolic argument(s) */

                        // when the operation is pending, it is not really a valid match
                        // for example, matching ``<env>... X |-> V ...</env>''
                        // against ``<env> Rho </env>'' will result in a pending
                        // choice operation due to the unknown ``Rho''.
                    } else {
                        if (nonLookupOrChoice instanceof Variable) {
                            Variable variable = (Variable) nonLookupOrChoice;
                            if (context.definition().subsorts().isSubsortedEq(variable.sort(), evalLookupOrChoice.sort())) {
                                Term term = crntSubst.put(variable, evalLookupOrChoice);
                                resolved = term == null || term.equals(evalLookupOrChoice);
                            }
                        } else {
                            // the non-lookup term is not a variable and thus requires further pattern matching
                            // for example: L:List[Int(#"0")] = '#ostream(_)(I:Int), where L is the output buffer
                            //           => '#ostream(_)(Int(#"1")) =? '#ostream(_)(I:Int)

                            Term evalNonLookupOrChoice = nonLookupOrChoice.substituteAndEvaluate(crntSubst, context);

                            PatternMatcher lookupMatcher = new PatternMatcher(rule.isLemma(), context);
                            if (lookupMatcher.patternMatch(evalLookupOrChoice, evalNonLookupOrChoice)) {
                                assert lookupMatcher.multiSubstitutions().isEmpty();

                                if (nonLookupOrChoice.variableSet().containsAll(lookupMatcher.substitution().keySet())) {
                                    resolved = true;
                                    crntSubst = composeSubstitution(crntSubst, lookupMatcher.substitution());
                                }
                            }
                        }
                    }

                    if (!resolved) {
                        crntSubst = null;
                        break;
                    }
        }


        /* evaluate side conditions */
        if (crntSubst != null) {
            Profiler.startTimer(Profiler.EVALUATE_REQUIRES_TIMER);
            for (Term require : rule.requires()) {
                // TODO(YilongL): in the future, we may have to accumulate
                // the substitution obtained from evaluating the side
                // condition
                Term evaluatedReq = require.substituteAndEvaluate(crntSubst, context);
                if (!evaluatedReq.equals(BoolToken.TRUE)) {
                    crntSubst = null;
                    break;
                }
            }
            Profiler.stopTimer(Profiler.EVALUATE_REQUIRES_TIMER);
        }

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
    public static List<Map<Variable, Term>> evaluateConditions(Rule rule, List<Map<Variable, Term>> substitutions,
            TermContext context) {
        /* handle fresh variables, data structure lookups, and side conditions */
        List<Map<Variable, Term>> results = Lists.newArrayList();
        for (Map<Variable, Term> crntSubst : substitutions) {
            crntSubst = evaluateConditions(rule, crntSubst, context);
            if (crntSubst != null) {
                results.add(crntSubst);
            }
        }
        return results;
    }

    public static Term evaluateLookupOrChoice(Term lookupOrChoice, Map<Variable, Term> subst, TermContext context) {
        Profiler.startTimer(Profiler.EVALUATE_LOOKUP_CHOICE_TIMER);
        Term evalLookupOrChoice = lookupOrChoice.copyOnShareSubstAndEval(subst, context);
        Profiler.stopTimer(Profiler.EVALUATE_LOOKUP_CHOICE_TIMER);
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

    public static List<SymbolicConstraint> getMultiConstraints(
            SymbolicConstraint constraint,
            List<List<SymbolicConstraint>> multiConstraints) {
        TermContext context = constraint.termContext();
        if (!multiConstraints.isEmpty()) {
            assert multiConstraints.size() <= 2;

            List<SymbolicConstraint> result = Lists.newArrayList();
            if (multiConstraints.size() == 1) {
                for (SymbolicConstraint cnstr : multiConstraints.get(0)) {
                    SymbolicConstraint composedCnstr = SymbolicConstraint
                            .simplifiedConstraintFrom(context, cnstr, constraint);
                    result.add(composedCnstr);
                }
            } else {
                List<SymbolicConstraint> constraints1 = multiConstraints.get(0);
                List<SymbolicConstraint> constraints2 = multiConstraints.get(1);
                for (SymbolicConstraint cnstr1 : constraints1) {
                    for (SymbolicConstraint cnstr2 : constraints2) {
                        SymbolicConstraint composedCnstr = SymbolicConstraint
                                .simplifiedConstraintFrom(context, constraint, cnstr1, cnstr2);
                        result.add(composedCnstr);
                    }
                }
            }
            return result;
        } else {
            // TODO(YilongL): no need to copy the constraint when it becomes immutable
            return Collections.singletonList(new SymbolicConstraint(constraint));
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

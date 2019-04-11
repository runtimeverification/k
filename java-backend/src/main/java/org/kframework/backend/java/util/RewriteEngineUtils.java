// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.Sets;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.InjectedKLabel;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemProjection;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.rewritemachine.RHSInstruction;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Equality;
import org.kframework.backend.java.symbolic.ImmutableMapSubstitution;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.RuleAuditing;
import org.kframework.backend.java.symbolic.Substitution;

import java.util.Collections;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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
            Term evalLookupOrChoice = construct(instructions, crntSubst, context);

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
                Term evaluatedReq = construct(rule.instructionsOfRequires().get(i), crntSubst, context);
                if (!evaluatedReq.equals(BoolToken.TRUE)) {
                    if (!evaluatedReq.isGround()
                            && context.getTopConstraint() != null
                            && context.getTopConstraint().implies(ConjunctiveFormula.of(context.global()).add(evaluatedReq, BoolToken.TRUE), Collections.emptySet(),
                            new FormulaContext(FormulaContext.Kind.FunctionRule, rule, context.global()))) {
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

        if (crntSubst != null) {
            ConjunctiveFormula substitutionAsFormula = ConjunctiveFormula.of(crntSubst, context.global())
                    .orientSubstitution(rule.matchingVariables());
            crntSubst = substitutionAsFormula.isMatching(rule.matchingVariables()) ? substitutionAsFormula.substitution() : null;
        }

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

    public static Term construct(List<RHSInstruction> rhsInstructions, Map<Variable, Term> solution, TermContext context) {
        GlobalContext global = context.global();

        /* Special case for one-instruction lists that can be resolved without a stack;
         * The code falls through the general case. */
        if (rhsInstructions.size() == 1) {
            RHSInstruction instruction = rhsInstructions.get(0);
            switch (instruction.type()) {
            case PUSH:
                return instruction.term();
            case SUBST:
                Variable var = (Variable) instruction.term();
                Term content = solution.get(var);
                if (content == null) {
                    content = var;
                }
                return content;
            }
        }

        Deque<Term> stack = new LinkedList<>();
        for (RHSInstruction instruction : rhsInstructions) {
            switch (instruction.type()) {
            case PUSH:
                Term t = instruction.term();
                stack.push(t);
                break;
            case CONSTRUCT:
                RHSInstruction.Constructor constructor = instruction.constructor();
                switch (constructor.type()) {
                case BUILTIN_LIST:
                    BuiltinList.Builder builder = BuiltinList.builder(constructor.assocListSort, constructor.assocListOperator, constructor.assocListUnit, global);
                    for (int i = 0; i < constructor.size1(); i++) {
                        builder.add(stack.pop());
                    }
                    stack.push(builder.build());
                    break;
                case BUILTIN_MAP:
                    BuiltinMap.Builder builder1 = BuiltinMap.builder(global);
                    for (int i = 0; i < constructor.size1(); i++) {
                        Term key = stack.pop();
                        Term value = stack.pop();
                        builder1.put(key, value);
                    }
                    for (int i = 0; i < constructor.size2(); i++) {
                        builder1.concatenate(stack.pop());
                    }
                    stack.push(builder1.build());
                    break;
                case BUILTIN_SET:
                    BuiltinSet.Builder builder2 = BuiltinSet.builder(global);
                    for (int i = 0; i < constructor.size1(); i++) {
                        builder2.add(stack.pop());
                    }
                    for (int i = 0; i < constructor.size2(); i++) {
                        builder2.concatenate(stack.pop());
                    }
                    stack.push(builder2.build());
                    break;
                case KITEM:
                    Term kLabel = stack.pop();
                    Term kList = stack.pop();
                    stack.push(KItem.of(kLabel, kList, global, constructor.att()));
                    break;
                case KITEM_PROJECTION:
                    stack.push(new KItemProjection(constructor.kind(), stack.pop()));
                    break;
                case KLABEL_INJECTION:
                    stack.push(new KLabelInjection(stack.pop()));
                    break;
                case INJECTED_KLABEL:
                    stack.push(new InjectedKLabel(stack.pop()));
                    break;
                case KLIST:
                    KList.Builder builder3 = KList.builder();
                    for (int i = 0; i < constructor.size1(); i++) {
                        builder3.concatenate(stack.pop());
                    }
                    stack.push(builder3.build());
                    break;
                case KSEQUENCE:
                    KSequence.Builder builder4 = KSequence.builder();
                    for (int i = 0; i < constructor.size1(); i++) {
                        builder4.concatenate(stack.pop());
                    }
                    stack.push(builder4.build());
                    break;
                default:
                    throw new AssertionError("unreachable");
                }
                break;
            case SUBST:
                Variable var = (Variable) instruction.term();
                Term term = solution.get(var);
                if (term == null) {
                    term = var;
                }
                stack.push(term);
                break;
            case EVAL:
                KItem kItem = (KItem) stack.pop();
                stack.push(kItem.resolveFunctionAndAnywhere(context));
                break;
            case PROJECT:
                KItemProjection projection = (KItemProjection) stack.pop();
                stack.push(projection.evaluateProjection());
                break;
            }
        }
        assert stack.size() == 1;
        return stack.pop();
    }
}

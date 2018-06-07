// Copyright (c) 2013-2016 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.CopyOnWriteTransformer;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.SymbolicRewriter;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.commons.lang3.tuple.Triple;


/**
 * Table of {@code public static} methods for builtin meta K operations.
 *
 * @author AndreiS
 */
public class MetaK {

    /**
     * Checks if two given {@link Term}s can be unified.
     *
     * @param term1
     *            the first term
     * @param term2
     *            the second term
     * @param context
     *            the term context
     * @return {@link BoolToken#TRUE} if the two terms can be unified;
     *         {@link BoolToken#FALSE} if they cannot be unified; otherwise,
     *         {@code null}
     */
    public static BoolToken unifiable(Term term1, Term term2, TermContext context) {
        ConjunctiveFormula constraint = ConjunctiveFormula.of(context.global());
        if (term1 instanceof KList && term2 instanceof KList) {
            if (((KList) term1).size() != ((KList) term2).size()) {
                return null;
            }
            for (int i = 0; i < ((KList) term1).size(); i++) {
                constraint = constraint.add(((KList) term1).get(i), ((KList) term2).get(i));
            }
        } else {
            constraint = constraint.add(term1, term2);
        }
        constraint = constraint.simplify(context);
        if (constraint.isFalse()) {
            return BoolToken.FALSE;
        }

        BoolToken result = BoolToken.FALSE;
        for (ConjunctiveFormula solution : constraint.getDisjunctiveNormalForm().conjunctions()) {
            solution = solution.simplify(context);
            if (solution.isSubstitution()) {
                return BoolToken.TRUE;
            } else if (!solution.isFalse()) {
                /* when none of the solutions is true and at least one of the
                 * them is not certainly false, the result is unknown */
                result = null;
            }
        }
        return result;
    }

    /**
     * Checks if the subject term matches the pattern.
     *
     * @param subject
     *            the subject term
     * @param pattern
     *            the pattern term
     * @param context
     *            the term context
     * @return {@link BoolToken#TRUE} if the two terms can be matched;
     *         otherwise, {@link BoolToken#FALSE}
     */
    public static BoolToken matchable(Term subject, Term pattern, TermContext context) {
        return PatternMatcher.matchable(subject, pattern, context) ? BoolToken.TRUE
                : BoolToken.FALSE;
    }

    /**
     * Renames {@link MetaVariable}s of a given {@link Term} to fresh {@link Variable}s if they appear also in
     * a given {@link BuiltinSet} of {@link MetaVariable}s.
     *
     *
     * @param term
     *            the given term
     * @param builtinSet
     *            the given set of meta variables
     * @param context
     *            the term context
     * @return the resulting term if the renaming succeeds; or the original term
     *         if the given {@code BuiltinSet} has a frame or contains not only
     *         {@code MetaVariable}s
     */
    public static Term rename(Term term, BuiltinSet builtinSet, TermContext context) {
        if (builtinSet.hasFrame() /* || !builtinSet.operations().isEmpty() */) {
            return term;
        }

        Set<Variable> variables = new HashSet<>();
        for (Term element : builtinSet.elements()) {
            if (!(element instanceof MetaVariable)) {
                return term;
            }

            variables.add(new Variable((MetaVariable) element));
        }

        term = (Term) term.accept(new CopyOnWriteTransformer() {
            @Override
            public JavaSymbolicObject<Term> transform(MetaVariable metaVariable) {
                return new Variable(metaVariable);
            }
        });

        return term.substitute(Variable.rename(variables));
    }

    /**
     * Renames all {@link Variable}s inside a given {@link Term} to unique fresh names.
     *
     * @param term
     *            the given term
     * @param context
     *            the term context
     * @return the resulting term after renaming
     */
    public static Term renameVariables(Term term, TermContext context) {
        Set<Variable> variables = term.variableSet();
        return term.substitute(Variable.rename(variables));
    }

    public static Term freezeVariables(Term termToFreeze, Term termWithBoundVars, TermContext context) {
        BuiltinSet variables = trueVariables(termWithBoundVars, context);
        return (Term) termToFreeze.accept(new CopyOnWriteTransformer(context) {
            @Override
            public JavaSymbolicObject<Term> transform(Variable variable) {
                if (!variables.contains(variable)) {
                    return new MetaVariable(variable);
                }
                return variable;
            }
        });
    }

    /**
     * Returns all {@link Variable}s inside a given {@link Term} as a
     * {@link BuiltinSet} of {@link MetaVariable}s.
     */
    public static BuiltinSet variables(Term term, TermContext context) {
        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        for (Variable variable : term.variableSet()) {
            builder.add(new MetaVariable(variable));
        }
        return (BuiltinSet) builder.build();
    }

    /**
     * Returns all {@link Variable}s inside a given {@link Term} as a
     * {@link BuiltinSet}.
     */
    public static BuiltinSet trueVariables(Term term, TermContext context) {
        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.addAll(term.variableSet());
        return (BuiltinSet) builder.build();
    }

    public static Term variablesMap(Term term, TermContext context) {
        BuiltinMap.Builder builder = BuiltinMap.builder(context.global());
        for (Variable variable : term.variableSet()) {
            builder.put(new MetaVariable(variable), variable);
        }
        return builder.build();
    }

    /**
     * Returns the K label of a specified {@link KItem}.
     *
     * @param kItem
     *            the specified {@code KItem}
     * @param context
     *            the term context
     * @return the K label
     */
    public static KItem getKLabel(KItem kItem, TermContext context) {
        // TODO(AndreiS): handle KLabel variables
        return KItem.of(new KLabelInjection(kItem.kLabel()), KList.EMPTY, context.global(),
            kItem.att());
    }

    public static Term configuration(TermContext context) {
        //return KLabelInjection.injectionOf(context.getTopTerm(), context.global());
        return context.getTopTerm();
    }

    public static BoolToken isConcrete(Term term, TermContext context) {
        return BoolToken.of(term.isConcrete());
    }

    public static BuiltinSet unify(ConstrainedTerm term1, ConstrainedTerm term2, TermContext context) {
        List<ConjunctiveFormula> results = term1.unify(term2, Collections.emptySet()).stream()
                .map(Triple::getLeft)
                .collect(Collectors.toList());
        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.addAll(results);
        return (BuiltinSet) builder.build();
    }

    public static BuiltinSet match(ConstrainedTerm subject, ConstrainedTerm pattern, TermContext context) {
        List<BuiltinMap> results = subject.unify(pattern, null).stream()
                .filter(Triple::getMiddle)
                .map(Triple::getLeft)
                .map(c -> {
                    assert c.isSubstitution();
                    return c.substitution().asBuiltinMap(context.global());
                })
                .collect(Collectors.toList());
        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.addAll(results);
        return (BuiltinSet) builder.build();
    }

    public static BuiltinSet rewrite(ConstrainedTerm term, TermContext context) {
        return step(term, false, context);
    }

    public static BuiltinSet narrow(ConstrainedTerm term, TermContext context) {
        return step(term, true, context);
    }

    private static BuiltinSet step(
            ConstrainedTerm term,
            boolean narrowing,
            TermContext context) {
        term.termContext().setCounterValue(context.getCounterValue());

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(context.global(), Collections.emptyList(), null);
        List<ConstrainedTerm> results = symbolicRewriter.fastComputeRewriteStep(
                term,
                false,
                narrowing,
                false);

        Optional<Long> updatedCounterValue = results.stream()
                .map(ConstrainedTerm::termContext)
                .map(TermContext::getCounterValue)
                .max(Comparator.comparing(Long::valueOf));
        updatedCounterValue.ifPresent(context::setCounterValue);

        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.addAll(results);
        return (BuiltinSet) builder.build();
    }


    public static Term and(Term term, ConjunctiveFormula constraint, TermContext context) {
        if (term instanceof ConstrainedTerm) {
            ConstrainedTerm constrainedTerm = (ConstrainedTerm) term;
            ConjunctiveFormula resultConstraint = constrainedTerm.constraint().add(constraint).simplify();
            Term resultTerm = constrainedTerm.term()
                    .substituteAndEvaluate(resultConstraint.substitution(), constrainedTerm.termContext());
            return new ConstrainedTerm(resultTerm, resultConstraint, constrainedTerm.termContext());
        } else if (term instanceof ConjunctiveFormula) {
            ConjunctiveFormula conjunctiveFormula = (ConjunctiveFormula) term;
            return conjunctiveFormula.add(constraint).simplify();
        } else {
            return new ConstrainedTerm(
                    term.substituteAndEvaluate(constraint.substitution(), context),
                    constraint,
                    context.fork());
        }
    }

    public static ConjunctiveFormula top(TermContext context) {
        return ConjunctiveFormula.of(context.global());
    }

    public static ConjunctiveFormula equal(Term leftHandSide, Term rightHandSide, TermContext context) {
        return ConjunctiveFormula.of(context.global()).add(leftHandSide, rightHandSide).simplify();
    }

    public static Term getTerm(ConstrainedTerm constrainedTerm, TermContext context) {
        return constrainedTerm.term();
    }

    public static ConjunctiveFormula getConstraint(ConstrainedTerm constrainedTerm, TermContext context) {
        return constrainedTerm.constraint();
    }

    public static BuiltinMap getSubstitution(ConjunctiveFormula constraint, TermContext context) {
        return constraint.substitution().asBuiltinMap(context.global());
    }

    public static BoolToken isSubstitution(ConjunctiveFormula constraint, TermContext context) {
        return BoolToken.of(constraint.isSubstitution());
    }
}

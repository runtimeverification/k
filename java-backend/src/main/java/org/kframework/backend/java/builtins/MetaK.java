// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.symbolic.CopyOnWriteTransformer;
import org.kframework.backend.java.symbolic.PatternMatcher;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.kil.ASTNode;

import java.util.HashSet;
import java.util.Set;


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
        SymbolicConstraint constraint = new SymbolicConstraint(context);
        constraint.add(term1, term2);
        constraint.simplify();
        if (constraint.isFalse()) {
            return BoolToken.FALSE;
        }

        BoolToken result = BoolToken.FALSE;
        for (SymbolicConstraint solution : constraint.getMultiConstraints()) {
            solution.simplify();
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

        Set<Variable> variables = new HashSet<Variable>();
        for (Term element : builtinSet.elements()) {
            if (!(element instanceof MetaVariable)) {
                return term;
            }

            variables.add(new Variable((MetaVariable) element));
        }

        term = (Term) term.accept(new CopyOnWriteTransformer(context) {
            @Override
            public ASTNode transform(MetaVariable metaVariable) {
                return new Variable(metaVariable);
            }
        });

        return KLabelInjection.injectionOf(term.substitute(Variable.getFreshSubstitution(variables), context), context);
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
        return term.substitute(Variable.getFreshSubstitution(variables), context);
    }

    public static Term freezeVariables(Term termToFreeze, Term termWithBoundVars, TermContext context) {
        BuiltinSet variables = trueVariables(termWithBoundVars, context);
        return KLabelInjection.injectionOf((Term) termToFreeze.accept(new CopyOnWriteTransformer(context) {
            @Override
            public ASTNode transform(Variable variable) {
                if (!variables.contains(variable)) {
                    return new MetaVariable(variable);
                }
                return variable;
            }
        }), context);
    }

    /**
     * Returns all {@link Variable}s inside a given {@link Term} as a
     * {@link BuiltinSet} of {@link MetaVariable}s.
     */
    public static BuiltinSet variables(Term term, TermContext context) {
        BuiltinSet.Builder builder = BuiltinSet.builder();
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
        BuiltinSet.Builder builder = BuiltinSet.builder();
        builder.addAll(term.variableSet());
        return (BuiltinSet) builder.build();
    }

    public static Term variablesMap(Term term, TermContext context) {
        BuiltinMap.Builder builder = BuiltinMap.builder();
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
        return KItem.of(new KLabelInjection(kItem.kLabel()), KList.EMPTY, context,
            kItem.getSource(), kItem.getLocation());
    }
}

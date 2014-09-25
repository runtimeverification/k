// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.CopyOnShareSubstAndEvalTransformer;
import org.kframework.backend.java.symbolic.Evaluator;
import org.kframework.backend.java.symbolic.Matchable;
import org.kframework.backend.java.symbolic.PatternExpander;
import org.kframework.backend.java.symbolic.SubstituteAndEvaluateTransformer;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.Unifiable;
import org.kframework.backend.java.util.Utils;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * A K term in the internal representation of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public abstract class Term extends JavaSymbolicObject implements Transformable, Matchable, Unifiable, Comparable<Term> {

    protected final Kind kind;
    // protected final boolean normalized;

    private Boolean mutable = null;

    protected Term(Kind kind) {
        this.kind = kind;
    }

    /**
     * Returns a {@link List} view of the indexing pairs from the {@code k}
     * cells of this {@code Term}.
     */
    public List<IndexingPair> getKCellIndexingPairs(final Definition definition) {
        final List<IndexingPair> indexingPairs = new ArrayList<IndexingPair>();
        accept(new BottomUpVisitor() {
            @Override
            public void visit(Cell cell) {
                if (cell.getLabel().equals(CellLabel.K)) {
                    indexingPairs.add(IndexingPair.getKCellIndexingPair(cell, definition));
                } else if (cell.contentKind().isStructural()) {
                    super.visit(cell);
                }
            }
        });
        return indexingPairs;
    }

    /**
     * Returns true if this term has exactly the sort returned by {@link #sort()},
     * and not any of its proper subsorts.
     *
     * @see #sort()
     */
    public abstract boolean isExactSort();

    /**
     * Returns {@code true} if a unification task between this term and another term cannot be
     * further decomposed into simpler unification tasks.
     */
    public abstract boolean isSymbolic();

    /**
     * Returns the kind of this term (Cell, CellCollection, KItem, K, KLabel, KList, or Map).
     */
    public Kind kind() {
        return kind;
    }

    public abstract Sort sort();

    /**
     * @return {@code true} if this term has {@code Cell} inside; otherwise,
     *         {@code false}
     */
    public final boolean isMutable() {
        if (mutable == null) {
            mutable = computeMutability();
        }
        return mutable;
    }

    /**
     * Checks if this term has {@code Cell} inside.
     */
    protected abstract boolean computeMutability();

    /**
     * Returns a new {@code Term} instance obtained from this term by evaluating
     * pending functions and predicates. <br>
     * TODO(YilongL): gradually eliminate the use of this method and switch to
     * the one with constraint, i.e., {@link this#evaluate(SymbolicConstraint,
     * TermContext)}.
     */
    public Term evaluate(TermContext context) {
        return evaluate(null, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by evaluating
     * pending functions and predicates.
     * <p>
     * This method carries a symbolic constraint as argument for two reasons: 1)
     * at the time when this method is called, the symbolic constraint
     * associated with the outer constrained term which contains this term may
     * not been properly simplified and normalized, which means the evaluation
     * process may still need the information of this constraint when performing
     * unification; 2) the evaluation process may create new constraints in
     * certain cases (e.g., in test generation).
     *
     * @param constraint
     *            the symbolic constraint of the {@link ConstrainedTerm} which
     *            contains this {@code Term}
     * @param context
     *            the term context
     * @return the result {@code Term} instance
     */
    public Term evaluate(SymbolicConstraint constraint, TermContext context) {
        return Evaluator.evaluate(this, constraint, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying a binder insensitive substitution.
     */
    @Override
    public Term substitute(Map<Variable, ? extends Term> substitution, TermContext context) {
        return (Term) super.substitute(substitution, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying a binder-aware substitution.
     */
    @Override
    public Term substituteWithBinders(Map<Variable, ? extends Term> substitution, TermContext context) {
        return (Term) super.substituteWithBinders(substitution, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying
     * substitution.
     * <p>
     * Note: for efficiency reason, this method will only evaluate functions
     * that become concrete due to the substitution. That is to say, concrete
     * pending functions are omitted by this method. In this case, use the
     * {@code evaluate} method instead.
     */
    public Term substituteAndEvaluate(Map<Variable, ? extends Term> substitution, TermContext context) {
        // TODO(AndreiS): disable the check below when proving things until this is properly fixed by Cosmin
        if (context.definition().context().krunOptions == null
                || context.definition().context().krunOptions.experimental.prove() == null) {
            // TODO(AndreiS): assert that there are not any unevaluated functions in this term
            if (substitution.isEmpty() || isGround()) {
                return this;
            }
        }

        // YilongL: comment out the slow implementation
//        SubstitutionTransformer transformer = new BinderSubstitutionTransformer(substitution, context);
//        transformer.getPostTransformer().addTransformer(new LocalEvaluator(context));
//        return (Term) accept(transformer);
        SubstituteAndEvaluateTransformer transformer = new SubstituteAndEvaluateTransformer(substitution, context);
        return (Term) this.accept(transformer);
    }

    /**
     * Similar to {@link Term#substituteAndEvaluate(Map, TermContext)} except
     * that this method will copy the terms used for substitution whenever
     * necessary in order to avoid undesired sharing of mutable terms.
     *
     * @param substitution
     *            the substitution map; TODO(YilongL): this may become a
     *            multi-map in the future when the pattern matching algorithm
     *            allows us to record multiple equal terms binding to a variable
     *            for the sake of maximizing term reuse
     * @param variablesToReuse
     *            a set of variables in the substitution whose binding terms can
     *            be reused to build the new term
     * @param context
     * @return a new term obtained by applying substitution
     */
    public Term copyOnShareSubstAndEval(
            Map<Variable, ? extends Term> substitution,
            Set<Variable> variablesToReuse, TermContext context) {
        if (substitution.isEmpty() || isGround()) {
            return this;
        }
        CopyOnShareSubstAndEvalTransformer transformer = new CopyOnShareSubstAndEvalTransformer(
                substitution, variablesToReuse, context);
        return (Term) this.accept(transformer);
    }

    /**
     * Similar to {@link Term#copyOnShareSubstAndEval(Map, Set, TermContext)}
     * except the empty reusable variable set.
     *
     * @see {@link Term#copyOnShareSubstAndEval(Map, Set, TermContext)}
     */
    public Term copyOnShareSubstAndEval(Map<Variable, ? extends Term> substitution, TermContext context) {
        return copyOnShareSubstAndEval(substitution, Collections.<Variable>emptySet(), context);
    }

    /**
     * Returns a list containing the contents of each occurrence of a cell with the given name.
     *
     * Warning: this is slow!
     * TODO(YilongL): improve performance when better indexing is available
     */
    public List<Term> getCellContentsByName(final CellLabel cellLabel) {
        final List<Term> contents = new ArrayList<>();
        accept(new BottomUpVisitor() {
            @Override
            public void visit(Cell cell) {
                super.visit(cell);
                if (cell.getLabel().equals(cellLabel)) {
                    contents.add(cell.getContent());
                }
            }
        });
        return contents;
    }

     /**
     * Returns a new {@code Term} instance obtained from this term by substituting variable with
     * term.
     */
    @Override
    public Term substituteWithBinders(Variable variable, Term term, TermContext context) {
        return (Term) super.substituteWithBinders(variable, term, context);
    }

    public Term expandPatterns(SymbolicConstraint constraint, boolean narrowing, TermContext context) {
        return PatternExpander.expand(this, constraint, narrowing, context);
    }

    @Override
    public final int compareTo(Term o) {
        return toString().compareTo(o.toString());
    }

    /**
     * Computes and caches the hashCode if it has not been computed yet.
     * Otherwise, simply returns the cached value.
     */
    @Override
    public final int hashCode() {
        if (hashCode == Utils.NO_HASHCODE) {
            hashCode = computeHash();
            hashCode = hashCode == 0 ? 1 : hashCode;
        }
        return hashCode;
    }

    /**
     * (Re-)computes the hashCode of this {@code Term}.
     * @return the hash code
     */
    protected abstract int computeHash();

    @Override
    public abstract boolean equals(Object object);
}

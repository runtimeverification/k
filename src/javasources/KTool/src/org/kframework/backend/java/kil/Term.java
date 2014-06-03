// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.symbolic.BinderSubstitutionTransformer;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.Evaluator;
import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.backend.java.symbolic.LocalEvaluator;
import org.kframework.backend.java.symbolic.Matchable;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.Unifiable;
import org.kframework.backend.java.util.Utils;
import org.kframework.utils.general.IndexingStatistics;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;


/**
 * A K term in the internal representation of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public abstract class Term extends JavaSymbolicObject implements Transformable, Matchable, Unifiable, Comparable<Term> {

    protected final Kind kind;
    // protected final boolean normalized;

    protected Term(Kind kind) {
        this.kind = kind;
    }

    /**
     * Translates a term from the generic KIL representation ({@link org.kframework.kil.Term}) to
     * Java Rewrite Engine internal representation ({@link org.kframework.backend.java.kil.Term}).
     */
    public static Term of(org.kframework.kil.Term kilTerm, Definition definition) {
        if (definition.context().javaExecutionOptions.indexingStats){
            IndexingStatistics.kilTransformationStopWatch.start();
        }

        KILtoBackendJavaKILTransformer transformer
                = new KILtoBackendJavaKILTransformer(definition.context());
        Term term = transformer.transformTerm(kilTerm, definition);

        if (definition.context().javaExecutionOptions.indexingStats){
            IndexingStatistics.kilTransformationStopWatch.stop();
        }
        return term;
    }

    /**
     * Returns a {@link List} view of the indexing pairs.
     */
    public List<IndexingPair> getIndexingPairs(final Definition definition) {
        final List<IndexingPair> indexingPairs = new ArrayList<IndexingPair>();
        accept(new BottomUpVisitor() {
            @Override
            public void visit(Cell cell) {
                if (cell.getLabel().equals("k")) {
                    indexingPairs.add(IndexingPair.getIndexingPair(cell.getContent(), definition));
                } else if (cell.contentKind() == Kind.CELL_COLLECTION) {
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

    /**
     * Returns a {@code String} representation of the sort of this object.
     */
    public abstract String sort();

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
        // TODO(AndreiS): assert that there are not any unevaluated functions in this term
        if (substitution.isEmpty() || isGround()) {
            return this;
        }

        SubstitutionTransformer transformer = new BinderSubstitutionTransformer(substitution, context);
        transformer.getPostTransformer().addTransformer(new LocalEvaluator(context));
        return (Term) accept(transformer);
    }

     /**
     * Returns a new {@code Term} instance obtained from this term by substituting variable with
     * term.
     */
    @Override
    public Term substituteWithBinders(Variable variable, Term term, TermContext context) {
        return (Term) super.substituteWithBinders(variable, term, context);
    }

    @Override
    public int compareTo(Term o) {
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
    public abstract int computeHash();
}

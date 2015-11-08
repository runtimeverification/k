// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.CopyOnShareSubstAndEvalTransformer;
import org.kframework.backend.java.symbolic.Evaluator;
import org.kframework.backend.java.symbolic.SubstituteAndEvaluateTransformer;
import org.kframework.backend.java.util.Constants;
import org.kframework.kore.convertors.KILtoInnerKORE;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * A K term in the internal representation of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public abstract class Term extends JavaSymbolicObject<Term> implements Comparable<Term>,
        org.kframework.kore.K {

    protected final Kind kind;
    // protected final boolean normalized;

    private Boolean mutable = null;

    protected Term(Kind kind) {
        super();
        this.kind = kind;
    }

    protected Term(Kind kind, Source source, Location location) {
        super(source, location);
        this.kind = kind;
    }

    /**
     * Returns a {@link List} view of the indexing pairs from the {@code k}
     * cells of this {@code Term}.
     */
    public List<IndexingPair> getKCellIndexingPairs(final Definition definition) {
        final List<IndexingPair> indexingPairs = new ArrayList<>();
        for (Term content : getCellContentsByName(CellLabel.K)) {
            indexingPairs.add(IndexingPair.getKCellIndexingPair(content, definition));
        }
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
        Boolean m = mutable;
        if (m == null) {
            mutable = m = computeMutability();
        }
        return m;
    }

    /**
     * Checks if this term has {@code Cell} inside.
     */
    protected abstract boolean computeMutability();

    /**
     * Returns a new {@code Term} instance obtained from this term by evaluating
     * pending functions and predicates. <br>
     */
    public Term evaluate(TermContext context) {
        return Evaluator.evaluate(this, context);
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
        return canSubstituteAndEvaluate(substitution) ?
               (Term) this.accept(new SubstituteAndEvaluateTransformer(substitution, context)) :
               this;
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
        if (!canSubstituteAndEvaluate(substitution)) {
            return this;
        }
        CopyOnShareSubstAndEvalTransformer transformer = new CopyOnShareSubstAndEvalTransformer(
                substitution, variablesToReuse, context);
        return (Term) this.accept(transformer);
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
            public void visit(CellCollection cellCollection) {
                for (CellCollection.Cell cell : cellCollection.get(cellLabel)) {
                    contents.add(cell.content());
                }
                for (CellCollection.Cell cell : cellCollection.cells().values()) {
                    if (cell.content() instanceof CellCollection) {
                        visit((CellCollection) cell.content());
                    }
                }
            }
        });
        return contents;
    }

    @Override
    public final int compareTo(Term o) {
        /* implement compareTo() in a way that the expensive toString() is
         * rarely called */
        if (hashCode() > o.hashCode()) {
            return 1;
        } else if (hashCode() < o.hashCode()) {
            return -1;
        } else if (equals(o)) {
            return 0;
        } else {
            /* Note: since the equality has been checked, it's okay that the
             * two different terms might have the same string representation */
            return toString().compareTo(o.toString());
        }
    }

    /**
     * Computes and caches the hashCode if it has not been computed yet.
     * Otherwise, simply returns the cached value.
     */
    @Override
    public final int hashCode() {
        int h = hashCode;
        if (h == Constants.NO_HASHCODE && !isMutable()) {
            h = computeHash();
            h = h == 0 ? 1 : h;
            hashCode = h;
        }
        return h;
    }

    /**
     * (Re-)computes the hashCode of this {@code Term}.
     * @return the hash code
     */
    protected abstract int computeHash();

    @Override
    public abstract boolean equals(Object object);

    public Att att() {
        return new KILtoInnerKORE(null, true).convertAttributes(this);
    }

    public Location location() { return getLocation(); }
    public Source source() { return getSource(); }
}

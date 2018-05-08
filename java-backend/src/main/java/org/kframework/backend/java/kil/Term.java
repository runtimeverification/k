// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.Evaluator;
import org.kframework.backend.java.symbolic.SubstituteAndEvaluateTransformer;
import org.kframework.backend.java.util.Constants;

import javax.annotation.Nonnull;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;


/**
 * A K term in the internal representation of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public abstract class Term extends JavaSymbolicObject<Term> implements Comparable<Term>,
        org.kframework.kore.K {

    protected final Kind kind;
    // protected final boolean normalized;

    protected Term(Kind kind) {
        super();
        this.kind = kind;
    }

    public Term(Kind kind, Att att) {
        super(att);
        this.kind = kind;
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
        return canSubstituteAndEvaluate(substitution, context.getTopConstraint()) ?
               (Term) this.accept(new SubstituteAndEvaluateTransformer(substitution, context)) :
               this;
    }

    /**
     * Returns a list containing the contents of each occurrence of a cell with the given name.
     *
     * Warning: this is slow!
     * TODO(YilongL): improve performance when better indexing is available
     */
    public List<Term> getCellContentsByName(final String cellLabel) {
        final List<Term> contents = new ArrayList<>();
        accept(new BottomUpVisitor() {
            @Override
            public void visit(KItem kItem) {
                if (kItem.kLabel().toString().equals(cellLabel)) {
                    contents.add(((KList) kItem.kList()).get(0));
                } else {
                    super.visit(kItem);
                }
            }
        });
        return contents;
    }

    @Override
    public final int compareTo(@Nonnull Term o) {
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
     * Otherwise, simply returns the cached javaBackendValue.
     */
    @Override
    public final int hashCode() {
        int h = hashCode;
        if (h == Constants.NO_HASHCODE) {
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

    public Location location() { return getLocation(); }
    public Source source() { return getSource(); }
}

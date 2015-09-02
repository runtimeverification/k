// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import com.google.common.base.Joiner;
import org.kframework.kore.K;


/**
 * Represents either a {@link KList} or a {@link KSequence}.
 *
 * @author AndreiS
 */
@SuppressWarnings("serial")
public abstract class KCollection extends Collection implements Iterable<Term>, org.kframework.kore.KCollection {

    protected KCollection(Variable frame, Kind kind) {
        super(frame, kind, null);
    }

    /**
     * Returns a view of the fragment of this {@code KCollection} that starts
     * from the specified {@code fromIndex}.
     *
     * @param fromIndex
     *            the start index of the fragment
     * @return a view of the specified fragment
     */
    public abstract Term fragment(int fromIndex);

    public final Term get(int index) {
        return getContents().get(index);
    }

    public abstract String getSeparatorName();
    public abstract String getIdentityName();

    public abstract List<Term> getContents();

    @Override
    public final Iterator<Term> iterator() {
        return getContents().iterator();
    }

    /**
     * Returns the size of the contents of this {@code KCollection}.
     *
     * @see {@link KCollection#contents}
     * @return the size of the contents
     */
    @Override
    public final int concreteSize() {
        return getContents().size();
    }

    @Override
    public final boolean isExactSort() {
        if (concreteSize() == 1) {
            return !hasFrame() && this.get(0).isExactSort();
        } else {
            /* 2 elements make a proper K collection */
            return true;
        }
    }

    @Override
    protected final int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + (frame == null ? 0 : frame.hashCode());
        hashCode = hashCode * Utils.HASH_PRIME + getContents().hashCode();
        return hashCode;
    }

    @Override
    protected final boolean computeMutability() {
        for (Term term : getContents()) {
            if (term.isMutable()) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(getSeparatorName());
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, getContents());
        if (super.frame != null) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(getSeparatorName());
            }
            stringBuilder.append(super.frame);
        }
        if (stringBuilder.length() == 0) {
            stringBuilder.append(getIdentityName());
        }
        return stringBuilder.toString();
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    /**
     * Promotes a given {@link Term} to a given {@link Kind}. The {@code Kind}s
     * involved in this method can only be {@code Kind#KITEM}, {@code Kind#K},
     * or {@code Kind#KLIST}. If the kind of the given {@code Term} is already
     * above or equal to the target {@code Kind}, do nothing.
     * <p>
     * To be more specific, a {@code KItem} can be promoted to a single-element
     * {@code KSequence} and, similarly, a {@code KSequence} can be promoted to
     * a single-element {@code KList}.
     *
     * @param term
     *            the given term to be promoted
     * @param kind
     *            the target kind that the term is to be promoted to
     * @return the resulting term after kind promotion
     */
    public static Term upKind(Term term, Kind kind) {
        assert term.kind() == Kind.KITEM || term.kind() == Kind.K || term.kind() == Kind.KLIST;
        assert kind == Kind.KITEM || kind == Kind.K || kind == Kind.KLIST;

        if (term.kind() == kind) {
            return term;
        }

        /* promote KItem to K */
        if (kind == Kind.K && term.kind() == Kind.KITEM) {
            return KSequence.singleton(term);
        }

        /* promote KItem or K to KList */
        if (kind == Kind.KLIST && (term.kind() == Kind.KITEM || term.kind() == Kind.K)) {
            return KList.singleton(term);
        }

        return term;
    }

    /**
     * Degrades a given {@link Term} to a given {@link Kind}. The {@code Kind}s
     * involved in this method can only be {@code Kind#KITEM}, {@code Kind#K},
     * or {@code Kind#KLIST}. If the kind of the given {@code Term} is already
     * lower than or equal to the target {@code Kind}, do nothing.
     * <p>
     * To be more specific, a single-element {@code KList} can be degraded to a
     * {@code KSequence} and, similarly, a single-element {@code KSequence} can
     * be degraded to a {@code KItem}.
     *
     * @param term
     *            the given term to be degraded
     * @return the resulting term after kind degradation
     */
    public static Term downKind(Term term) {
        assert term.kind() == Kind.KITEM || term.kind() == Kind.K || term.kind() == Kind.KLIST;

        if (term instanceof KList && !((KList) term).hasFrame() && ((KList) term).concreteSize() == 1) {
            term = ((KList) term).get(0);
        }

        if (term instanceof KSequence && !((KSequence) term).hasFrame() && ((KSequence) term).concreteSize() == 1) {
            term = ((KSequence) term).get(0);
        }

        return term;
    }

    @Override
    public List<K> items() {
        return (List<K>) (Object) getContents();
    }

    @Override
    public Stream<K> stream() {
        return items().stream();
    }

    public int size() {
        return items().size();
    }
}

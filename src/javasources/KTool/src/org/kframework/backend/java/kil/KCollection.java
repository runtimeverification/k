package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


/**
 * Represents either a {@link KList}, a {@link KSequence}, or a
 * {@link KCollectionFragment}.
 * 
 * @author AndreiS
 */
@SuppressWarnings("serial")
public abstract class KCollection extends Collection implements Iterable<Term> {

    /**
     * A list of {@code Term}s contained in this {@code KCollection}.
     */
    protected final ImmutableList<Term> contents;

    protected KCollection(ImmutableList<Term> items, Variable frame, Kind kind) {
        super(frame, kind);

        List<Term> normalizedItems = new ArrayList<Term>();
        for (Term term : items) {
            // TODO (AndreiS): fix KItem projection
            if (!(term instanceof Variable) && !(term instanceof KItemProjection) && (term.kind() == kind)) {
                assert term instanceof KCollection :
                        "associative use of KCollection(" + items + ", " + frame + ")";

                KCollection kCollection = (KCollection) term;

                assert !kCollection.hasFrame() : "associative use of KCollection";

                normalizedItems.addAll(kCollection.getContents());
            } else {
                normalizedItems.add(term);
            }
        }
        this.contents = ImmutableList.copyOf(normalizedItems);
    }

    /*
    protected KCollection(ListIterator<Term> itemsIterator, Variable frame, String kind) {
        super(frame, kind);
        this.items = new ArrayList<Term>();
        while (itemsIterator.hasNext()) {
            items.add(itemsIterator.next());
        }
    }*/

    protected KCollection(Variable frame, Kind kind) {
        super(frame, kind);
        this.contents = ImmutableList.of();
    }

    /**
     * Returns a view of the fragment of this {@code KCollection} that starts
     * from the specified {@code fromIndex}.
     * 
     * @param fromIndex
     *            the start index of the fragment
     * @return a view of the specified fragment
     */
    public abstract KCollection fragment(int fromIndex);

    public Term get(int index) {
        return contents.get(index);
    }

    public abstract String getSeparatorName();
    public abstract String getIdentityName();

    public ImmutableList<Term> getContents() {
        return contents;
    }

    @Override
    public Iterator<Term> iterator() {
        return contents.iterator();
    }

    /**
     * Returns the size of the contents of this {@code KCollection}.
     * 
     * @see {@link KCollection#contents}
     * @return the size of the contents
     */
    @Override
    public int size() {
        return contents.size();
    }

    @Override
    public boolean isExactSort() {
        if (contents.size() == 1) {
            return !hasFrame() && contents.get(0).isExactSort();
        } else {
            /* 2 elements make a proper K collection */
            return true;
        }
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + (frame == null ? 0 : frame.hashCode());
            hashCode = hashCode * Utils.HASH_PRIME + contents.hashCode();
        }
        return hashCode;
    }
    
    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }
        
        if (!(object instanceof KCollection)) {
            return false;
        }
        
        KCollection kCollection = (KCollection) object;
        return (frame == null ? kCollection.frame == null : frame
                .equals(kCollection.frame))
                && contents.equals(kCollection.contents);
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(getSeparatorName());
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, contents);
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

        /* promote KItem to K, and then promote K to KList */
        if (term.kind() == Kind.KITEM && (kind == Kind.K || kind == Kind.KLIST)) {
            term = new KSequence(ImmutableList.of(term));
        }

        if (term.kind() == Kind.K && kind == Kind.KLIST) {
            term = new KList(ImmutableList.of(term));
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

        if (term instanceof KList && !((KList) term).hasFrame() && ((KList) term).size() == 1) {
            term = ((KList) term).get(0);
        }

        if (term instanceof KSequence && !((KSequence) term).hasFrame() && ((KSequence) term).size() == 1) {
            term = ((KSequence) term).get(0);
        }

        return term;
    }

}

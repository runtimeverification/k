package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


/**
 * @author AndreiS
 */
public abstract class KCollection extends Collection implements Iterable<Term> {

    protected final ImmutableList<Term> items;

    protected KCollection(ImmutableList<Term> items, Variable frame, Kind kind) {
        super(frame, kind);

        List<Term> normalizedItems = new ArrayList<Term>();
        for (Term term : items) {
            if (term.kind() == kind) {
                assert term instanceof KCollection : "associative use of KCollection";

                KCollection kCollection = (KCollection) term;

                assert !kCollection.hasFrame() : "associative use of KCollection";

                normalizedItems.addAll(kCollection.getItems());
            } else {
                normalizedItems.add(term);
            }
        }
        this.items = ImmutableList.copyOf(normalizedItems);
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
        this.items = ImmutableList.of();
    }

    public abstract KCollection fragment(int length);

    public Term get(int index) {
        return items.get(index);
    }

    public abstract String getOperatorName();
    public abstract String getIdentityName();

    public ImmutableList<Term> getItems() {
        return items;
    }

    @Override
    public Iterator<Term> iterator() {
        return items.iterator();
    }

    public int size() {
        return items.size();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + (super.frame == null ? 0 : super.frame.hashCode());
        hash = hash * Utils.HASH_PRIME + items.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(getOperatorName());
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, items);
        if (super.frame != null) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(getOperatorName());
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

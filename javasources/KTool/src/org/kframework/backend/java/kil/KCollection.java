package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Iterator;


/**
 * @author AndreiS
 */
public abstract class KCollection extends Collection implements Iterable<Term> {

    protected final ImmutableList<Term> items;

    protected KCollection(ImmutableList<Term> items, Variable frame, Kind kind) {
        super(frame, kind);
        this.items = items;
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

}

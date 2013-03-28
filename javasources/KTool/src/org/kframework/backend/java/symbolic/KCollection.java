package org.kframework.backend.java.symbolic;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;

import org.kframework.kil.ASTNode;

import java.util.Iterator;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/17/13
 * Time: 1:03 PM
 * To change this template use File | Settings | File Templates.
 */
public abstract class KCollection extends Collection implements Iterable<Term> {

    protected final ImmutableList<Term> items;

    protected KCollection(ImmutableList<Term> items, Variable frame, String kind) {
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

    protected KCollection(Variable frame, String kind) {
        super(frame, kind);
        this.items = ImmutableList.of();
    }

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
    public String toString() {
        Joiner joiner = Joiner.on(getOperatorName());
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, items);
        if (super.hasFrame()) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(getOperatorName());
            }
            stringBuilder.append(super.getFrame());
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

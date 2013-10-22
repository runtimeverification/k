package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Iterator;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 10:22 AM
 * To change this template use File | Settings | File Templates.
 */
public class KCollectionFragment extends KCollection {

    private final int index;
    private final KCollection kCollection;

    public KCollectionFragment(KCollection kCollection, int index) {
        super(kCollection.getItems(),
              kCollection.hasFrame() ? kCollection.frame() : null,
              kCollection.kind());

        assert 0 <= index && index <= kCollection.size();

        this.kCollection = kCollection;
        this.index = index;
    }

    @Override
    public KCollection fragment(int length) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public Term get(int index) {
        assert index >= this.index;

        return items.get(index);
    }

    public int getIndex() {
        return index;
    }

    public KCollection getKCollection() {
        return kCollection;
    }

    @Override
    public String getOperatorName() {
        return kCollection.getOperatorName();
    }

    @Override
    public String getIdentityName() {
        return kCollection.getIdentityName();
    }

    @Override
    public ImmutableList<Term> getItems() {
        throw  new UnsupportedOperationException();
    }

    @Override
    public Iterator<Term> iterator() {
        return items.listIterator(index);
    }

    @Override
    public int size() {
        return items.size() - index;
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(getOperatorName());
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, items.subList(index, items.size()));
        if (super.hasFrame()) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(getOperatorName());
            }
            stringBuilder.append(super.frame());
        }
        if (stringBuilder.length() == 0) {
            stringBuilder.append(getIdentityName());
        }
        return stringBuilder.toString();
    }

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        throw new UnsupportedOperationException();
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

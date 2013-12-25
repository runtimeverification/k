package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Iterator;


/**
 * Represents a fragment of a {@link KCollection}.
 * 
 * @author AndreiS
 */
@SuppressWarnings("serial")
public class KCollectionFragment extends KCollection {

    private final int index;
    private final KCollection kCollection;

    public KCollectionFragment(KCollection kCollection, int index) {
        super(kCollection.getContents(),
              kCollection.hasFrame() ? kCollection.frame() : null,
              kCollection.kind());

        assert 0 <= index && index <= kCollection.size();

        this.kCollection = kCollection;
        this.index = index;
    }

    /**
     * Not supported in this class.
     */
    @Override
    public KCollection fragment(int length) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term get(int index) {
        assert index >= this.index;

        return contents.get(index);
    }

    public int getIndex() {
        return index;
    }

    public KCollection getKCollection() {
        return kCollection;
    }

    @Override
    public String getSeparatorName() {
        return kCollection.getSeparatorName();
    }

    @Override
    public String getIdentityName() {
        return kCollection.getIdentityName();
    }

    @Override
    public ImmutableList<Term> getContents() {
        throw  new UnsupportedOperationException();
    }

    @Override
    public Iterator<Term> iterator() {
        return contents.listIterator(index);
    }

    @Override
    public int size() {
        return contents.size() - index;
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(getSeparatorName());
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, contents.subList(index, contents.size()));
        if (super.hasFrame()) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(getSeparatorName());
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

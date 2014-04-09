package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;

import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.Iterator;


/**
 * Represents a fragment of a {@link KCollection}.
 * 
 * @author AndreiS
 */
@SuppressWarnings("serial")
public class KCollectionFragment extends KCollection {

    private final int startIndex;
    private final KCollection kCollection;
    
    private String sort;

    public KCollectionFragment(KCollection kCollection, int startIndex) {
        super(kCollection.getContents(),
              kCollection.hasFrame() ? kCollection.frame() : null,
              kCollection.kind());

        assert 0 <= startIndex && startIndex <= kCollection.size();

        this.kCollection = kCollection;
        this.startIndex = startIndex;
    }

    /**
     * Not supported in this class.
     */
    @Override
    public KCollection fragment(int fromIndex) {
        throw new UnsupportedOperationException();
    }
    
    @Override
    public String sort() {
        if (sort != null) {
            return sort;
        }

        sort =  startIndex < size() && !hasFrame() ? contents.get(startIndex).sort() : kCollection.sort();
        return sort;
    }

    @Override
    public Term get(int index) {
        assert index >= this.startIndex;

        return contents.get(index);
    }

    public int getStartIndex() {
        return startIndex;
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
        return contents.listIterator(startIndex);
    }

    @Override
    public int size() {
        return contents.size() - startIndex;
    }
    
    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = super.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + startIndex;
        }
        return hashCode;
    }
    
    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }
        
        if (!(object instanceof KCollectionFragment)) {
            return false;
        }
        
        KCollectionFragment kCollectionFragment = (KCollectionFragment) object;
        return startIndex == kCollectionFragment.startIndex
                && kCollection.equals(kCollectionFragment.kCollection);
    }
        
    @Override
    public String toString() {
        Joiner joiner = Joiner.on(getSeparatorName());
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, contents.subList(startIndex, contents.size()));
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
    public void accept(Unifier unifier, Term pattern) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
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

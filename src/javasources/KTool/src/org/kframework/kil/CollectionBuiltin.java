// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;

import java.util.Collection;
import java.util.Collections;

/**
 *
 *
 * @author AndreiS
 */
public class CollectionBuiltin extends DataStructureBuiltin {

    private final Collection<Term> elements;

    public CollectionBuiltin(
            DataStructureSort sort,
            Collection<Term> baseTerms,
            Collection<Term> elements) {
        super(sort, baseTerms);
        this.elements = elements;
    }

    public static CollectionBuiltin of(DataStructureSort sort,
                                       Collection<Term> baseTerms,
                                       Collection<Term> elements) {
        if (sort.type().equals(KSorts.LIST)) {
            return new CollectionBuiltin(sort, baseTerms, elements);
        }
        return new SetBuiltin(sort, baseTerms, elements);
    }

    public Collection<Term> elements() {
        return Collections.unmodifiableCollection(elements);
    }

    @Override
    public boolean isEmpty() {
        return elements.isEmpty() && super.baseTerms.isEmpty();
    }

    @Override
    public Term shallowCopy() {
        return new CollectionBuiltin(dataStructureSort, baseTerms, elements);
    }
    
    @Override
    public DataStructureBuiltin shallowCopy(Collection<Term> baseTerms) {
        return shallowCopy(baseTerms, elements);
    }
    
    public CollectionBuiltin shallowCopy(Collection<Term> baseTerms, Collection<Term> elements) {
        return new CollectionBuiltin(dataStructureSort, baseTerms, elements);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + super.hashCode();
        hash = hash * Context.HASH_PRIME + elements.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof CollectionBuiltin)) {
            return false;
        }

        CollectionBuiltin collectionBuiltin = (CollectionBuiltin) object;
        return super.equals(collectionBuiltin) && elements.equals(collectionBuiltin.elements);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Collection<Term> getChildren(
            DataStructureBuiltin.ListChildren type) {
        switch (type) {
            case ELEMENTS:
                return elements;
            default:
                return super.getChildren(type);
        }
    }

}

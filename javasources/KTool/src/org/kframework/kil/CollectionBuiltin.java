package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

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
            Collection<Term> elements,
            Collection<Term> terms) {
        super(sort, terms);
        this.elements = elements;
    }

    public static CollectionBuiltin of(DataStructureSort sort,
                                       Collection<Term> elements,
                                       Collection<Term> terms) {
        if (sort.type().equals(KSorts.LIST)) {
            return new CollectionBuiltin(sort, elements, terms);
        }
        return new SetBuiltin(sort, elements, terms);
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
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
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
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;


/**
 * A builtin map.
 *
 * @author AndreiS
 */
public class MapBuiltin extends CollectionBuiltin {

    private final LinkedHashMap<Term, Term> elements;

    public MapBuiltin(CollectionSort sort, LinkedHashMap<Term, Term> elements, Collection<Term> terms) {
        super(sort, terms);
        this.elements = elements;
    }

    public Map<Term, Term> elements() {
        return Collections.unmodifiableMap(elements);
    }

    @Override
    public boolean isEmpty() {
        return elements.isEmpty() && terms.isEmpty();
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * org.kframework.kil.loader.Context.HASH_PRIME + super.hashCode();
        hash = hash * Context.HASH_PRIME + elements.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof MapBuiltin)) {
            return false;
        }

        MapBuiltin mapBuiltin = (MapBuiltin) object;
        return super.equals(mapBuiltin) && elements.equals(mapBuiltin.elements);
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

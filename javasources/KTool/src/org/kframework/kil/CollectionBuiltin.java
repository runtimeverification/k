package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;


/**
 * Abstract class representing a builtin collection (bag, list, map and set).
 *
 * @author AndreiS
 */
public abstract class CollectionBuiltin extends Term {

    public static CollectionBuiltin empty(CollectionSort collectionSort) {
        if (collectionSort.type().equals(KSorts.MAP)) {
            return new MapBuiltin(
                    collectionSort,
                    new LinkedHashMap<Term, Term>(0),
                    Collections.<Term>emptyList());
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    public static CollectionBuiltin element(CollectionSort collectionSort, Term ... argument) {
        if (collectionSort.type().equals(KSorts.MAP)) {
            assert argument.length == 2:
                   "unexpected number of map item arguments; expected 2, found " + argument.length;
            LinkedHashMap<Term, Term> elements = new LinkedHashMap<Term, Term>(1);
            elements.put(argument[0], argument[1]);
            return new MapBuiltin(collectionSort, elements, Collections.<Term>emptyList());
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    public static CollectionBuiltin of(CollectionSort collectionSort, Term ... argument) {
        for (Term term : argument) {
            assert term.getSort().equals(collectionSort.name());
        }

        if (collectionSort.type().equals(KSorts.MAP)) {
            LinkedHashMap<Term, Term> elements = new LinkedHashMap<Term, Term>();
            List<Term> terms = new ArrayList<Term>();

            for (Term term : argument) {
                if (term instanceof MapBuiltin) {
                    MapBuiltin mapBuiltin = (MapBuiltin) term;
                    elements.putAll(mapBuiltin.elements());
                    terms.addAll(mapBuiltin.terms());
                } else {
                    terms.add(term);
                }
            }

            return new MapBuiltin(collectionSort, elements, terms);
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    protected final CollectionSort collectionSort;
    protected final Variable frame;
    protected final Collection<Term> terms;

    protected CollectionBuiltin(CollectionSort collectionSort, Collection<Term> terms) {
        this.collectionSort = collectionSort;
        this.terms = terms;
        if (terms.size() == 1) {
            Term term = terms.iterator().next();
            if (term instanceof Variable && term.getSort().equals(collectionSort.name())) {
                frame = (Variable) term;
            } else {
                frame = null;
            }
        } else {
            frame = null;
        }
    }

    public CollectionSort collectionSort() {
        return collectionSort;
    }

    public Variable frame() {
        assert hasFrame();

        return frame;
    }

    public boolean hasFrame() {
        return frame != null;
    }

    public boolean isElementCollection() {
        return terms.isEmpty();
    }

    public abstract boolean isEmpty();

    public Collection<Term> terms() {
        return Collections.unmodifiableCollection(terms);
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * org.kframework.kil.loader.Context.HASH_PRIME + sort.hashCode();
        hash = hash * Context.HASH_PRIME + terms.hashCode();
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
        return sort.equals(collectionBuiltin.sort) && terms.equals(collectionBuiltin.terms);
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
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

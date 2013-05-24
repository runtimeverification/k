package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;


/**
 * Abstract class representing a builtin data structure (bag, list, map or set).
 *
 * @author AndreiS
 */
public abstract class DataStructureBuiltin extends Term {

    public static DataStructureBuiltin empty(DataStructureSort sort) {
        if (sort.type().equals(KSorts.BAG)
                || sort.type().equals(KSorts.LIST)
                || sort.type().equals(KSorts.SET)) {
            return new CollectionBuiltin(sort,
                    Collections.<Term>emptyList(),
                    Collections.<Term>emptyList());
        } else if (sort.type().equals(KSorts.MAP)) {
            return new MapBuiltin(
                    sort,
                    Collections.<Term, Term>emptyMap(),
                    Collections.<Term>emptyList());
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    public static DataStructureBuiltin element(DataStructureSort sort, Term ... argument) {
        if (sort.type().equals(KSorts.BAG)
                || sort.type().equals(KSorts.LIST)
                || sort.type().equals(KSorts.SET)) {
            assert argument.length == 1:
                    "unexpected number of collection item arguments; expected 1, found "
                    + argument.length;

            return new CollectionBuiltin(
                    sort,
                    Collections.singletonList(argument[0]),
                    Collections.<Term>emptyList());
        } else if (sort.type().equals(KSorts.MAP)) {
            assert argument.length == 2:
                   "unexpected number of map item arguments; expected 2, found " + argument.length;

            return new MapBuiltin(
                    sort,
                    Collections.singletonMap(argument[0], argument[1]),
                    Collections.<Term>emptyList());
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    public static DataStructureBuiltin of(DataStructureSort sort, Term ... argument) {
        assert argument != null;
        for (Term term : argument) {
            assert term.getSort().equals(sort.name()):
                   "unexpected sort " + term.getSort() + " of term " + term + "at "
                   + term.getLocation() + "; "
                   + "expected " + sort.name();
        }

        if (sort.type().equals(KSorts.BAG)
                || sort.type().equals(KSorts.LIST)
                || sort.type().equals(KSorts.SET)) {
            Collection<Term> elements = new ArrayList<Term>();
            Collection<Term> terms = new ArrayList<Term>();
            for (Term term : argument) {
                if (term instanceof CollectionBuiltin) {
                    CollectionBuiltin collectionBuiltin = (CollectionBuiltin) term;
                    elements.addAll(collectionBuiltin.elements());
                    terms.addAll(collectionBuiltin.terms());
                } else {
                    terms.add(term);
                }
            }

            return new CollectionBuiltin(sort, elements, terms);
        } else if (sort.type().equals(KSorts.MAP)) {
            Map<Term, Term> elements = new HashMap<Term, Term>();
            Collection<Term> terms = new ArrayList<Term>();
            for (Term term : argument) {
                if (term instanceof MapBuiltin) {
                    MapBuiltin mapBuiltin = (MapBuiltin) term;
                    elements.putAll(mapBuiltin.elements());
                    terms.addAll(mapBuiltin.terms());
                } else {
                    terms.add(term);
                }
            }

            return new MapBuiltin(sort, elements, terms);
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    protected final DataStructureSort dataStructureSort;
    protected final Variable frame;
    protected final Collection<Term> terms;

    protected DataStructureBuiltin(DataStructureSort sort, Collection<Term> terms) {
        super(sort.name());
        this.dataStructureSort = sort;
        this.terms = terms;
        if (terms.size() == 1) {
            Term term = terms.iterator().next();
            if (term instanceof Variable && term.getSort().equals(sort.name())) {
                frame = (Variable) term;
            } else {
                frame = null;
            }
        } else {
            frame = null;
        }
    }

    public DataStructureSort sort() {
        return dataStructureSort;
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

        if (!(object instanceof DataStructureBuiltin)) {
            return false;
        }

        DataStructureBuiltin dataStructureBuiltin = (DataStructureBuiltin) object;
        return sort.equals(dataStructureBuiltin.sort) && terms.equals(dataStructureBuiltin.terms);
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

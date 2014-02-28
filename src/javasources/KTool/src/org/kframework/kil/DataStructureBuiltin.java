package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;


/**
 * Abstract class representing a data structure (bag, list, map or set) AST node.
 *
 * A data structure node must be a union (bag, map, set) or concatenation (list) of:
 * <p>
 * (1) variables of the data structure sort, represented by {@link Variable} instances;
 * (2) data structure operations, represented by {@link KApp} instances (e.g. {@code keys(M)}
 *     with {@code M} a variable of some sort hooked to the builtin map);
 * (3) elements (bag, list, set) or entries (map).
 * </p>
 * Nodes of the first and second kinds are stored in the {@code baseTerms} collection field of
 * this class. Nodes of the last kind are stored in fields in the particular classes representing
 * each of the builtin data structures (class which extends this class).
 *
 * A data structure may be used unrestrictedly in the right-hand side or condition of a rule.
 * However, a data structure used in the left-hand side of a rule must be restricted to at most one
 * variable (node of the first kind) and no operations (nodes of the second kind),
 * while it may contain arbitrary many elements or entries. This restriction enables matching a
 * data structure pattern.
 *
 * @see DataStructureSort
 *
 * @author AndreiS
 */
public abstract class DataStructureBuiltin extends Term {

    public static DataStructureBuiltin empty(DataStructureSort sort) {
        if (sort.type().equals(KSorts.BAG)
                || sort.type().equals(KSorts.SET)) {
            return new SetBuiltin(sort,
                    Collections.<Term>emptyList(),
                    Collections.<Term>emptyList());
        } else if (sort.type().equals(KSorts.LIST)) {
            return new ListBuiltin(sort,
                    Collections.<Term>emptyList(),
                    Collections.<Term>emptyList(), Collections.<Term>emptyList());
        } else if (sort.type().equals(KSorts.MAP)) {
            return new MapBuiltin(
                    sort,
                    Collections.<Term>emptyList(),
                    Collections.<Term, Term>emptyMap());
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

            if (sort.type().equals(KSorts.LIST)) {
                ListBuiltin l = new ListBuiltin(
                        sort,
                        Collections.<Term>emptyList(),
                        Collections.singletonList(argument[0]),
                        Collections.<Term>emptyList());
                return l;
            } else {
                return new SetBuiltin(sort,
                        Collections.<Term>emptyList(),
                        Collections.singletonList(argument[0]));
            }
        } else if (sort.type().equals(KSorts.MAP)) {
            assert argument.length == 2:
                   "unexpected number of map item arguments; expected 2, found " + argument.length;

            return new MapBuiltin(
                    sort,
                    Collections.<Term>emptyList(),
                    Collections.singletonMap(argument[0], argument[1]));
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    public static DataStructureBuiltin of(DataStructureSort sort, Term ... argument) {
        /* TODO(AndreiS): enforce some type checking for collections
        assert argument != null;
        for (Term term : argument) {
            assert term.getSort().equals(sort.name()):
                   "unexpected sort " + term.getSort() + " of term " + term + "at "
                   + term.getLocation() + "; "
                   + "expected " + sort.name();
        }
        */

        if (sort.type().equals(KSorts.BAG)
                || sort.type().equals(KSorts.SET)) {
            Collection<Term> elements = new ArrayList<Term>();
            Collection<Term> terms = new ArrayList<Term>();
            for (Term term : argument) {
                if (term instanceof CollectionBuiltin) {
                    CollectionBuiltin collectionBuiltin = (CollectionBuiltin) term;
                    elements.addAll(collectionBuiltin.elements());
                    terms.addAll(collectionBuiltin.baseTerms());
                } else {
                    terms.add(term);
                }
            }

            return new SetBuiltin(sort, terms, elements);
        } else if (sort.type().equals(KSorts.LIST)) {
            ArrayList<Term> elementsLeft = new ArrayList<Term>();
            ArrayList<Term> elementsRight = new ArrayList<Term>();
            ArrayList<Term> terms = new ArrayList<Term>();

            int leftIndex;
            for (leftIndex = 0; leftIndex < argument.length; ++leftIndex) {
                if (!(argument[leftIndex] instanceof ListBuiltin)) {
                    break;
                }
                ListBuiltin listBuiltin = (ListBuiltin) argument[leftIndex];

                if (!listBuiltin.baseTerms().isEmpty()) {
                    break;
                }
                elementsLeft.addAll(listBuiltin.elementsLeft());
                elementsLeft.addAll(listBuiltin.elementsRight());
            }

            int rightIndex;
            for (rightIndex = argument.length - 1; rightIndex > leftIndex; --rightIndex) {
                if (!(argument[rightIndex] instanceof ListBuiltin)) {
                    break;
                }
                ListBuiltin listBuiltin = (ListBuiltin) argument[rightIndex];

                if (!listBuiltin.baseTerms().isEmpty()) {
                    break;
                }

                for (Term element : listBuiltin.elementsRight()) {
                    elementsRight.add(0, element);
                }
                for (Term element : listBuiltin.elementsLeft()) {
                    elementsRight.add(0, element);
                }
            }

            if (leftIndex == rightIndex && argument[rightIndex] instanceof ListBuiltin) {
                ListBuiltin listBuiltin = (ListBuiltin) argument[leftIndex];
                elementsLeft.addAll(listBuiltin.elementsLeft());
                for (Term element : listBuiltin.elementsRight()) {
                    elementsRight.add(0, element);
                }
            } else {
                terms.addAll(Arrays.asList(argument).subList(leftIndex, rightIndex + 1));
            }

            return ListBuiltin.of(sort, elementsLeft, elementsRight, terms);
        } else if (sort.type().equals(KSorts.MAP)) {
            Map<Term, Term> elements = new HashMap<Term, Term>();
            Collection<Term> terms = new ArrayList<Term>();
            for (Term term : argument) {
                if (term instanceof MapBuiltin) {
                    MapBuiltin mapBuiltin = (MapBuiltin) term;
                    elements.putAll(mapBuiltin.elements());
                    terms.addAll(mapBuiltin.baseTerms());
                } else {
                    terms.add(term);
                }
            }

            return new MapBuiltin(sort, terms, elements);
        } else {
            assert false : "unknown collection type";
            return null;
        }
    }

    protected final DataStructureSort dataStructureSort;
    /**
     * The single variable allowed in this data structure if occurring in the
     * left-hand side of a rule. Set to {@code null} if this data structure can
     * not occur in the left-hand side or is a collection of elements or
     * entries; otherwise, it must be the only element in {@code baseTerms}.
     * 
     * @see DataStructureBuiltin
     */
    protected final Variable viewBase;
    /**
     * {@code Collection} of {@link KApp} AST nodes (representing data structure
     * operations) and {@link Variable} AST nodes.
     * 
     * @see DataStructureBuiltin
     */
    protected final Collection<Term> baseTerms;

    protected DataStructureBuiltin(DataStructureSort sort, Collection<Term> baseTerms) {
        super(sort.name());
        this.dataStructureSort = sort;
        this.baseTerms = baseTerms;
        if (baseTerms.size() == 1) {
            Term term = baseTerms.iterator().next();
            if (term instanceof Variable && term.getSort().equals(sort.name())) {
                viewBase = (Variable) term;
            } else {
                viewBase = null;
            }
        } else {
            viewBase = null;
        }
    }

    public Collection<Term> baseTerms() {
        return Collections.unmodifiableCollection(baseTerms);
    }

    public boolean hasViewBase() {
        return viewBase != null;
    }

    public boolean isElementCollection() {
        return baseTerms.isEmpty();
    }

    public abstract boolean isEmpty();

    /**
     * Returns {@code true} if this data structure may occur in the left-hand side of a rule.
     */
    public boolean isLHSView() {
        /*
         * the two cases where this data structure builtin can appear in the LHS
         * of a rule: 1) viewBase != null => viewBase is the only element in
         * baseTerms; 2) viewBase == null && baseTerms.isEmpty() => this data
         * structure builtin is a collection of elements/entries
         */
        return viewBase != null || baseTerms.isEmpty();
    }

    public DataStructureSort sort() {
        return dataStructureSort;
    }

    public Variable viewBase() {
        assert hasViewBase();

        return viewBase;
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + sort.hashCode();
        hash = hash * Context.HASH_PRIME + baseTerms.hashCode();
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
        return sort.equals(dataStructureBuiltin.sort)
               && baseTerms.equals(dataStructureBuiltin.baseTerms);
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
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

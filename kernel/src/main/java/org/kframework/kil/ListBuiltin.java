// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.Collection;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;

/**
 * A builtin list
 *
 * @author TraianSF
 */
public class ListBuiltin extends CollectionBuiltin {
    private final List<Term> elementsRight;

    private ListBuiltin(DataStructureSort sort, List<Term> baseTerms, List<Term> elementsLeft,
                       List<Term> elementsRight) {
        super(sort, baseTerms, elementsLeft);
        this.elementsRight = elementsRight;
    }

    public List<Term> elementsLeft() {
        return elements();
    }

    public List<Term> elementsRight() {
        return Collections.unmodifiableList(elementsRight);
    }

    @Override
    public List<Term> elements() {
        return Collections.unmodifiableList((List<Term>) elements);
    }

    @Override
    public List<Term> baseTerms() {
        return Collections.unmodifiableList((List<Term>) baseTerms);
    }

    @Override
    public DataStructureBuiltin shallowCopy(Collection<Term> terms) {
        return ListBuiltin.of(sort(), (List<Term>)terms, elementsLeft(), elementsRight());
    }

    @Override
    public CollectionBuiltin shallowCopy(Collection<Term> terms,
            Collection<Term> elements) {
        return ListBuiltin.of(sort(), (List<Term>)terms, (List<Term>)elements, elementsRight());
    }

    public static ListBuiltin of(DataStructureSort sort, List<Term> terms, List<Term> elementsLeft,
                       List<Term> elementsRight) {
        ArrayList<Term> left = new ArrayList<Term>(elementsLeft);
        ArrayList<Term> base = new ArrayList<Term>();
        ArrayList<Term> right = new ArrayList<Term>();
        if (!terms.isEmpty()) {
            if (terms.get(0) instanceof ListBuiltin
                    || terms.get(terms.size() - 1) instanceof ListBuiltin) {
                ListBuiltin nestedListBuiltin = (ListBuiltin) DataStructureBuiltin.of(sort,
                        terms.toArray(new Term[terms.size()]));
                left.addAll(nestedListBuiltin.elementsLeft());
                base.addAll(nestedListBuiltin.baseTerms());
                right.addAll(nestedListBuiltin.elementsRight());
            } else {
                base.addAll(terms);
            }
        }
        right.addAll(elementsRight);
        if (base.isEmpty()) {
            left.addAll(right);
            right.clear();
        }
        return new ListBuiltin(sort, base, left, right);
    }

    @Override
    public String toString() {
        return elements().toString() + baseTerms().toString() + elementsRight.toString();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }


    @Override
    public Collection<Term> getChildren(DataStructureBuiltin.ListChildren type) {
        switch (type) {
            case ELEMENTS_RIGHT:
                return elementsRight;
            default:
                return super.getChildren(type);
        }
    }

    @Override
    public Term toKApp(Context context) {
        List<Term> items = new ArrayList<>();
        for (Term element : elementsLeft()) {
            items.add(KApp.of(DataStructureSort.DEFAULT_LIST_ITEM_LABEL, element));
        }
        for (Term base : baseTerms()) {
            items.add(base);
        }
        for (Term element : elementsRight()) {
            items.add(KApp.of(DataStructureSort.DEFAULT_LIST_ITEM_LABEL, (Term) element));
        }
        return toKApp(items);
    }

}

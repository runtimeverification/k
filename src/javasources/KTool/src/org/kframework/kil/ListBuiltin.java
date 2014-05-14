// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.Collection;
import java.util.ArrayList;
import java.util.Collections;

import org.kframework.kil.visitors.Visitor;

/**
 * A builtin list
 *
 * @author TraianSF
 */
public class ListBuiltin extends CollectionBuiltin {
    private final Collection<Term> elementsRight;

    public ListBuiltin(DataStructureSort sort, Collection<Term> baseTerms, Collection<Term> elementsLeft,
                       Collection<Term> elementsRight) {
        super(sort, baseTerms, elementsLeft);
        this.elementsRight = elementsRight;
    }

    public Collection<Term> elementsLeft() {
        return elements();
    }

    public Collection<Term> elementsRight() {
        return Collections.unmodifiableCollection(elementsRight);
    }
    
    @Override
    public DataStructureBuiltin shallowCopy(Collection<Term> terms) {
        return ListBuiltin.of(sort(), elementsLeft(), elementsRight(), terms);
    }
    
    @Override
    public CollectionBuiltin shallowCopy(Collection<Term> terms,
            Collection<Term> elements) {
        return ListBuiltin.of(sort(), elements, elementsRight(), terms);
    }

    // TODO(YilongL): shouldn't elementsLeft and elementsRight have type java.util.List?
    public static ListBuiltin of(DataStructureSort sort, Collection<Term> elementsLeft, Collection<Term> elementsRight,
                       Collection<Term> terms) {
        ArrayList<Term> left = new ArrayList<Term>(elementsLeft);
        ArrayList<Term> base = new ArrayList<Term>();
        ArrayList<Term> right = new ArrayList<Term>();
        boolean lhs = true;
        for (Term term : terms) {
            if (term instanceof ListBuiltin) {
                ListBuiltin listBuiltin = (ListBuiltin) term;
                assert listBuiltin.sort().equals(sort) : "inner lists are expected to have the same sort for now, found " + sort + " and " + listBuiltin.sort();
//              Recurse to make sure there are no additional nested inner ListBuiltins
                listBuiltin = ListBuiltin.of(listBuiltin.sort(), listBuiltin.elementsLeft(), listBuiltin.elementsRight(),
                        listBuiltin.baseTerms());
                Collection<Term> listBuiltinBase = listBuiltin.baseTerms();
                Collection<Term> listBuiltinLeft = listBuiltin.elementsLeft();
                Collection<Term> listBuiltinRight = listBuiltin.elementsRight();
                if (lhs) {
                    left.addAll(listBuiltinLeft);
                    if (!listBuiltinBase.isEmpty()) {
                        lhs = false;
                        base.addAll(listBuiltinBase);
                        right.addAll(listBuiltinRight);
                    } else {
                        left.addAll(listBuiltinRight);
                    }
                } else {
                    assert listBuiltinLeft.isEmpty() : "left terms no longer allowed here";
                    if (!listBuiltinBase.isEmpty()) {
                        assert right.isEmpty() : "we cannot add base terms if right terms have been already added";
                        assert listBuiltinLeft.isEmpty() : "inner list cannot have elements on the left";
                        base.addAll(listBuiltinBase);
                    } else {
                        right.addAll(listBuiltinLeft);
                    }
                    right.addAll(listBuiltinRight);
                }
            } else {
                lhs = false;
                base.add(term);
            }
        }
        right.addAll(elementsRight);
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

}

package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collection;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

/**
 * A builtin list
 *
 * @author TraianSF
 */
public class ListBuiltin extends CollectionBuiltin {
    private final Collection<Term> elementsRight;

    public ListBuiltin(DataStructureSort sort, Collection<Term> elementsLeft, Collection<Term> elementsRight,
                       Collection<Term> terms) {
        super(sort, elementsLeft, terms);
        this.elementsRight = elementsRight;
    }

    public Collection<Term> elementsLeft() {
        return elements();
    }

    public Collection<Term> elementsRight() {
        return Collections.unmodifiableCollection(elementsRight);
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

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
        return new ListBuiltin(sort, left, right, base);
    }

    @Override
    public String toString() {
        return elements().toString() + baseTerms().toString() + elementsRight.toString();
    }
}

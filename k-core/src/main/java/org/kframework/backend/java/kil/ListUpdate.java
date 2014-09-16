// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.List;
import com.google.common.collect.ImmutableList;

/**
 *
 * @author AndreiS
 */
public class ListUpdate extends Term implements DataStructureUpdate {

    /** {@link Term} representation of the list */
    private final Term list;
    /** number of elements to be removed from the left of the list */
    private final int removeLeft;
    /** number of elements to be removed from the right of the list */
    private final int removeRight;

    public ListUpdate(Term list, int removeLeft, int removeRight) {
        super(Kind.KITEM);
        this.list = list;
        this.removeLeft = removeLeft;
        this.removeRight = removeRight;
    }

    public Term evaluateUpdate() {
        if (!(list instanceof BuiltinList)) {
            return this;
        }
        BuiltinList builtinList = (BuiltinList) list;

        int pendingRemoveLeft;
        int pendingRemoveRight;
        List<Term> elementsLeft = builtinList.elementsLeft();
        List<Term> elementsRight = builtinList.elementsRight();
        if (builtinList.isConcreteCollection()) {
            if (removeLeft + removeRight > elementsLeft.size()) {
                return Bottom.of(Kind.KITEM);
            }

            pendingRemoveLeft = pendingRemoveRight = 0;
            elementsLeft = elementsLeft.subList(removeLeft, elementsLeft.size() - removeRight);
            elementsRight = ImmutableList.of();
        } else {
            if (removeLeft > elementsLeft.size()) {
                pendingRemoveLeft = removeLeft - elementsLeft.size();
                elementsLeft = ImmutableList.of();
            } else {
                pendingRemoveLeft = 0;
                elementsLeft = elementsLeft.subList(removeLeft, elementsLeft.size());
            }

            if (removeRight > elementsRight.size()) {
                pendingRemoveRight = removeRight - elementsRight.size();
                elementsRight = ImmutableList.of();
            } else {
                pendingRemoveRight = 0;
                elementsRight = elementsRight.subList(0, elementsRight.size() - removeRight);
            }
        }

        BuiltinList.Builder builder = BuiltinList.builder();
        builder.addItems(elementsLeft);
        builder.concatenate(builtinList.baseTerms());
        builder.addItems(elementsRight);

        return (pendingRemoveLeft > 0 || pendingRemoveRight > 0) ?
                new ListUpdate(builder.build(), pendingRemoveLeft, pendingRemoveLeft) :
                builder.build();
    }

    public Term list() {
        return list;
    }

    public int removeLeft() {
        return removeLeft;
    }

    public int removeRight() {
        return removeRight;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public Sort sort() {
        return list.sort();
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + list.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + removeLeft;
        hashCode = hashCode * Utils.HASH_PRIME + removeRight;
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ListUpdate)) {
            return false;
        }

        ListUpdate listUpdate = (ListUpdate) object;
        return list.equals(listUpdate.list)
                && removeLeft == listUpdate.removeLeft
                && removeRight == listUpdate.removeRight;
    }

    @Override
    public String toString() {
        return "remove(" + list.toString() + ", " + removeLeft + ", " + removeRight + ")";
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        // TODO(YilongL): throw an exception instead?
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}

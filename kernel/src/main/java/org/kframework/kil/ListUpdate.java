// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;

import java.util.Collection;
import java.util.Collections;

/**
 * Builtin List update operation.
 *
 * @author TraianSF (refactoring from {@link SetUpdate})
 */
public class ListUpdate extends Term implements Interfaces.Collection<Term, ListUpdate.ListChildren> {

    /** {@link Variable} name of the set */
    private final Variable base;

    /** {@code List} of entries to be removed from the list */
    private final Collection<Term> removeLeft;
    private final Collection<Term> removeRight;

    public static enum ListChildren {
        REMOVE_LEFT,
        REMOVE_RIGHT
    }

    public ListUpdate(Variable base, Collection<Term> removeLeft, Collection<Term> removeRight) {
        super(base.getSort());
        this.base = base;
        this.removeLeft = removeLeft;
        this.removeRight = removeRight;
    }

    public Variable base() {
        return base;
    }

    public Collection<Term> removeLeft() {
        return Collections.unmodifiableCollection(removeLeft);
    }

    public Collection<Term> removeRight() {
        return Collections.unmodifiableCollection(removeRight);
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + base.hashCode();
        hash = hash * Context.HASH_PRIME + removeLeft.hashCode();
        hash = hash * Context.HASH_PRIME + removeRight.hashCode();
        return hash;
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
        return base.equals(listUpdate.base)
                && removeLeft == listUpdate.removeLeft && removeRight == listUpdate.removeRight;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Collection<Term> getChildren(ListChildren type) {
        switch (type) {
            case REMOVE_LEFT:
                return removeLeft;
            case REMOVE_RIGHT:
                return removeRight;
            default:
                throw new AssertionError("unreachable");
        }
    }
}

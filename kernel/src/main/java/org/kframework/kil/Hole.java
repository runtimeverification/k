// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/**
 * Represents {@code HOLE} in context declarations.
 * See {@link FreezerHole} for holes in freezers.
 */
public class Hole extends Term {

    public static final Hole KITEM_HOLE = new Hole(Sort.KITEM);

    public Hole(Element element) {
        super(element);
        this.sort = Sort.KITEM; //Sort.of(element.getAttribute(Constants.SORT_sort_ATTR));
    }

    private Hole(Hole hole) {
        super(hole);
    }

    public Hole(Sort sort) {
        super(sort);

        assert sort.equals(Sort.KITEM);
    }

    public String toString() {
        return "[]:" + sort + " ";
    }

    @Override
    public Hole shallowCopy() {
        return new Hole(this);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof Hole))
            return false;
        Hole hole = (Hole)obj;

        return this.sort.equals(hole.getSort());
    }

    @Override
    public int hashCode() {
        return sort.hashCode();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}

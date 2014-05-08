// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/** The hole in a {@link Freezer}.
 * See {@link Hole} for the syntax of contexts.
 */
public class FreezerHole extends Term {
    /** Currently always zero, until nested freezers are implemented */
    private int index;
    
    public FreezerHole(int index) {
        super("K");
        this.index = index;
    }
    
    public FreezerHole(Element element) {
        // TODO: for Radu
        super(element);
    }

    @Override
    public Term shallowCopy() {
        return new FreezerHole(this.index);
    }
    
    public int getIndex() {
        return index;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof FreezerHole)) return false;
        FreezerHole f = (FreezerHole)o;
        return index == f.index;
    }

    @Override
    public int hashCode() {
        return index;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}

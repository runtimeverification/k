// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.Collections;
import java.util.List;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/** Set contents have sort Set or SetItem */
public class Set extends Collection {

    public static final Set EMPTY = new Set(Collections.<Term> emptyList());

    public Set(Element element) {
        super(element);
    }

    public Set(Set node) {
        super(node);
    }

    public Set(String location, String filename) {
        super(location, filename, "Set");
    }

    public Set(List<Term> col) {
        super("Set", col);
    }

    public Set() {
        super("Set");
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Set shallowCopy() {
        return new Set(this);
    }

}

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import java.util.Collections;


/** An associative list of terms of sort List or ListItem */
public class List extends Collection {

    public static final List EMPTY = new List(Collections.<Term>emptyList());

    public List(Element element) {
        super(element);
    }

    public List(List node) {
        super(node);
    }

    public List(String location, String filename) {
        super(location, filename, "List");
    }

    public List() {
        super("List");
    }

    public List(java.util.List<Term> col) {
        super("List", col);
    }

    @Override
    public String toString() {
        return super.toString();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public List shallowCopy() {
        return new List(this);
    }
}

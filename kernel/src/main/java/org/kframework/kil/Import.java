// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** An import directive */
public class Import extends ModuleItem {

    String name;

    public Import(String importName) {
        super();
        name = importName;
    }

    public Import(Import import1) {
        super(import1);
        this.name = import1.name;
    }

    @Override
    public String toString() {
        return "  imports " + name;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    @Override
    public Import shallowCopy() {
        return new Import(this);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}

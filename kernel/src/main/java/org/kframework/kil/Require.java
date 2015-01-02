// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** A require directive */
public class Require extends DefinitionItem {
    /** The string argument to {@code require}, as written in the input file. */
    private String value;

    public Require(Require require) {
        super(require);
        value = require.value;
    }

    public Require(String value) {
        super();
        this.value = value;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    public void setValue(String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public Require shallowCopy() {
        return new Require(this);
    }

    @Override
        public String toString() {
          return "require \""+value+"\"";
        }
}

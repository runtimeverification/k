// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

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

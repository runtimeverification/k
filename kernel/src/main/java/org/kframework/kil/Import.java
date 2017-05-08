// Copyright (c) 2012-2016 K Team. All Rights Reserved.
package org.kframework.kil;

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
}

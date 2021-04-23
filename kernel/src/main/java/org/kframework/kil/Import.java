// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

/** An import directive */
public class Import extends ModuleItem {

    String name;

    public Import(String importName) {
        super();
        name = importName;
    }

    public Import(String importName, Location loc, Source source) {
        super(loc, source);
        this.name = importName;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("  imports ");
        sb.append(name);
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }
}

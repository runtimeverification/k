// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

import org.w3c.dom.Element;

public abstract class ModuleItem extends ASTNode {
    public ModuleItem(ModuleItem s) {
        super(s);
    }

    public ModuleItem(Element elem) {
        super(elem);
    }

    public ModuleItem() {
        super();
    }

    public ModuleItem(Location loc, Source source) {
        super(loc, source);
    }

    public java.util.List<String> getLabels() {
        return null;
    }

    public java.util.List<String> getKLabels() {
        return null;
    }

}

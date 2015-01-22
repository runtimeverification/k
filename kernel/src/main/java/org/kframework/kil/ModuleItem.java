// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

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

    public java.util.List<String> getLabels() {
        return null;
    }

    public java.util.List<String> getKLabels() {
        return null;
    }

    public java.util.List<Sort> getAllSorts() {
        return null;
    }
}

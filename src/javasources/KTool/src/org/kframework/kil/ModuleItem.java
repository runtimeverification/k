// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

public abstract class ModuleItem extends ASTNode {
    public ModuleItem(ModuleItem s) {
        super(s);
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

    public java.util.List<String> getAllSorts() {
        return null;
    }
}

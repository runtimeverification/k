// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.util.ArrayList;

import org.kframework.kil.Import;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectIncludesVisitor extends BasicVisitor {
    public CollectIncludesVisitor(Context context) {
        super(context);
    }

    private java.util.List<Import> importList = new ArrayList<Import>();

    public Void visit(Import i, Void _) {
        importList.add(i);
        return null;
    }

    public Void visit(ModuleItem mi, Void _) {
        return null;
    }

    public java.util.List<Import> getImportList() {
        return importList;
    }

    public void setImportList(java.util.List<Import> importList) {
        this.importList = importList;
    }
}

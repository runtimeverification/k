// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kagreg;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectImportsVisitor extends BasicVisitor {
    protected List<Import> imports;
    protected boolean collectPredefined;
    protected int inPredefined;

    public CollectImportsVisitor(Context context, boolean collectPredefined) {
        super(context);
        imports = new ArrayList<Import>();
        this.collectPredefined = collectPredefined;
    }

    @Override
    public Void visit(Module module, Void _) {
        if (module.isPredefined()) {
            inPredefined++;
        }
        super.visit(module, _);
        if (module.isPredefined()) {
            inPredefined--;
        }
        return null;
    }

    @Override
    public Void visit(Import node, Void _) {
        if (collectPredefined || inPredefined == 0) {
            imports.add(node);
        }
        return null;
    }

    public List<Import> getImports() {
        return imports;
    }
}

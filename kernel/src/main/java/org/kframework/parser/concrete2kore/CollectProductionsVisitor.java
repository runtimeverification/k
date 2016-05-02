// Copyright (c) 2014-2016 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectProductionsVisitor extends BasicVisitor {
    public CollectProductionsVisitor(Context context) {
        super(context);
    }

    private String moduleName;
    private Sort sort;

    public Void visit(Module mod, Void _void) {
        this.moduleName = mod.getName();
        return super.visit(mod, _void);
    }

    public Void visit(Syntax syntax, Void _void) {
        this.sort = syntax.getDeclaredSort().getRealSort();
        return super.visit(syntax, _void);
    }

    @Override
    public Void visit(Production node, Void _void) {
        node.setSort(sort);
        node.setOwnerModuleName(moduleName);
        context.addProduction(node);
        this.getCurrentModule().getModuleContext().addProduction(node);
        return null;
    }
}

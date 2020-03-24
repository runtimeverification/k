// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kore.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;

import java.util.List;

public class CollectProductionsVisitor {
    private final Context context;
    private final boolean kore;

    public CollectProductionsVisitor(boolean kore, Context context) {
        this.kore = kore; this.context = context;
    }

    private String moduleName;
    private Sort sort;
    private List<Sort> params;

    public void visit(Module mod) {
        this.moduleName = mod.getName();
        mod.getItems().forEach(mi -> { if (mi instanceof Syntax) visit((Syntax)mi); });
    }

    public void visit(Syntax syntax) {
        this.sort = syntax.getDeclaredSort().getRealSort();
        this.params = syntax.getParams();
        syntax.getPriorityBlocks().forEach(pb -> pb.getProductions().forEach(this::visit));
    }

    public void visit(Production node) {
        node.setSort(sort);
        node.setOwnerModuleName(moduleName);
        node.setParams(params);
        context.addProduction(node, kore);
    }

    public void visit(Definition def) {
        def.getItems().forEach(di -> { if (di instanceof Module) visit((Module)di); });
    }
}

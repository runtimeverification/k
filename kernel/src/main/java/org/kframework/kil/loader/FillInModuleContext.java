// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.Poset;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

public class FillInModuleContext extends BasicVisitor {

    public FillInModuleContext() {
        super(FillInModuleContext.class.toString(), null);
    }

    @Override
    public Void visit(Definition def, Void _void)  {
        super.visit(def, _void);

        // calculate the transitivity using DFS from the main module
        Set<Module> visited = new HashSet<>();
        DFS(def.getDefinitionContext().getModuleByName(def.getMainModule()), visited);
        return null;
    }

    private void DFS(Module start, Set<Module> visited) {
        if (!visited.contains(start)) {
            visited.add(start);
            for (Module next : new HashSet<>(start.getModuleContext().getImportedModules())) {
                DFS(next, visited);
                // add everything from the included module to the context of the current one
                start.getModuleContext().add(next.getModuleContext());
            }
        }
    }

    @Override
    public Void visit(Import node, Void _void)  {
        Module module;
        // TODO(dwightguth) remove only the condition the same time with maude backend
        if (!node.getName().startsWith("#")) { // maude legacy: some modules specified with # are builtin
            module = this.getCurrentDefinition().getDefinitionContext().getModuleByName(node.getName());
            if (module == null) {
                String msg = "Could not find module: " + node.getName() + " imported from: " + this.getCurrentModule().getName();
                throw KExceptionManager.compilerError(msg, this, node);
            }
            this.getCurrentModule().getModuleContext().addImportedModule(module);
        }
        return null;
    }

    @Override
    public Void visit(Syntax syn, Void _void)  {
        this.getCurrentModule().getModuleContext().addDeclaredSort(syn.getDeclaredSort().getSort());
        super.visit(syn, _void);
        return null;
    }

    @Override
    public Void visit(Production node, Void _void) {
        if (node.isSyntacticSubsort())
            this.getCurrentModule().getModuleContext().addSyntacticSubsort(node.getSort(), node.getSubsort());
        this.getCurrentModule().getModuleContext().addProduction(node);
        super.visit(node, _void);
        return null;
    }
}

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

    private boolean autoinclude;
    private Poset<String> moduleInclusion = new Poset<>();
    public FillInModuleContext(boolean autoinclude) {
        super(FillInModuleContext.class.toString(), null);
        this.autoinclude = autoinclude;
    }

    @Override
    public Void visit(Definition def, Void _)  {
        super.visit(def, _);
        if (def.getMainSyntaxModule().equals(def.getMainModule())) {
            // if the syntax module is the same with the main module, add everything
            def.getModulesMap().get(def.getMainModule()).getModuleContext().addImportedModule(this.getCurrentDefinition().getModulesMap().get(Constants.AUTO_INCLUDED_MODULE));
            moduleInclusion.addRelation(def.getModulesMap().get(def.getMainModule()).getName(), Constants.AUTO_INCLUDED_MODULE);
        }
        List<String> circuit = moduleInclusion.checkForCycles();
        if (circuit != null) {
            String msg = "Found circularity in module imports: ";
            for (String moduleName : circuit)
                msg += moduleName + " < ";
            msg += circuit.get(0);
            throw KExceptionManager.compilerError(msg, this, def);
        }
        // TODO: transitive closure for imports
        // DFS from the main module

        Set<Module> visited = new HashSet<>();
        DFS(def.getModulesMap().get(def.getMainModule()), visited);
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
    public Void visit(Import node, Void _)  {
        Module module;
        if (!node.getName().startsWith("#")) { // maude legacy: some modules specified with # are builtin
            module = this.getCurrentDefinition().getModulesMap().get(node.getName());
            if (module == null) {
                String msg = "Could not find module: " + node.getName() + " imported from: " + this.getCurrentModule().getName();
                throw KExceptionManager.compilerError(msg, this, node);
            }
            this.getCurrentModule().getModuleContext().addImportedModule(module);
        }
        moduleInclusion.addRelation(this.getCurrentModule().getName(), node.getName());
        return null;
    }

    @Override
    public Void visit(Module node, Void _) {
        if (autoinclude) {
            if (this.getCurrentDefinition().getMainSyntaxModule().equals(node.getName())) {
                // the syntax module automatically includes Constants.AUTO_INCLUDED_SYNTAX_MODULE
                node.getModuleContext().addImportedModule(this.getCurrentDefinition().getModulesMap().get(Constants.AUTO_INCLUDED_SYNTAX_MODULE));
                moduleInclusion.addRelation(node.getName(), Constants.AUTO_INCLUDED_SYNTAX_MODULE);
                // TODO: (RaduM) try to figure out how and when to import the autoincluded modules.
            } else if (!node.isPredefined()) {
                // every user defined module automatically includes Constants.AUTO_INCLUDED_MODULE
                node.getModuleContext().addImportedModule(this.getCurrentDefinition().getModulesMap().get(Constants.AUTO_INCLUDED_MODULE));
                moduleInclusion.addRelation(node.getName(), Constants.AUTO_INCLUDED_MODULE);
            }
        }
        super.visit(node, _);
        return null;
    }

    @Override
    public Void visit(Syntax syn, Void _)  {
        this.getCurrentModule().getModuleContext().addDeclaredSort(syn.getDeclaredSort().getSort());
        super.visit(syn, _);
        return null;
    }

    @Override
    public Void visit(Production node, Void _) {
        if (node.isSyntacticSubsort())
            this.getCurrentModule().getModuleContext().addSyntacticSubsort(node.getSort(), node.getSubsort());
        this.getCurrentModule().getModuleContext().addProduction(node);
        super.visit(node, _);
        return null;
    }
}

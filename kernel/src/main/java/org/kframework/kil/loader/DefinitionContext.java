// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Module;
import org.kframework.utils.Poset;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class DefinitionContext implements Serializable {
    private Map<String, Module> modulesMap = new HashMap<>();
    private Poset<String> modules = Poset.create();

    public void addModule(Module m) {
        modulesMap.put(m.getName(), m);
    }

    public void addModules(Collection<Module> modules) {
        for (Module m : modules)
            modulesMap.put(m.getName(), m);
    }

    public void setModules(Collection<DefinitionItem> dis) {
        modulesMap.clear();
        for (DefinitionItem di : dis) {
            if (di instanceof Module)
            modulesMap.put(((Module) di).getName(), (Module) di);
        }
    }

    public boolean containsModule(String name) {
        return modulesMap.containsKey(name);
    }

    public Module getModuleByName(String name) {
        return modulesMap.get(name);
    }

    public void addModuleImport(String mainModule, String importedModule) {
        if (mainModule.equals(importedModule))
            return;
        modules.addRelation(mainModule, importedModule);
    }

    public boolean isModuleIncludedEq(String localModule, String importedModule) {
        if (localModule.equals(importedModule))
            return true;
        return modules.isInRelation(localModule, importedModule);
    }

    public void finalizeModules() {
        List<String> circuit = modules.checkForCycles();
        if (circuit != null) {
            String msg = "Found circularity in module imports: ";
            for (String moduleName : circuit)
                msg += moduleName + " < ";
            msg += circuit.get(0);
            throw KExceptionManager.compilerError(msg);
        }
        modules.transitiveClosure();
    }
}

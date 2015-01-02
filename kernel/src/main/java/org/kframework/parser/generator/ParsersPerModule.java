// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.Context;
import org.kframework.parser.concrete2.Grammar;
import org.kframework.parser.concrete2.KSyntax2GrammarStatesFilter;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * For each module, collect the included modules and create a new parser.
 */
public class ParsersPerModule {

    /**
     * Generates a Map of moduleName -> programParser for the entire definition
     * given as argument.
     * @param def        The definition for which to generate all the program parsers.
     * @param context    The Context object, with all the helper methods.
     * @return Map of moduleName -> programParser
     */
    public static  Map<String, Grammar> generateParsersForModules(Definition def, Context context, KExceptionManager kem) {
        Map<String, Grammar> parsers = new HashMap<>();
        for (DefinitionItem di : def.getItems()) {
            if (di instanceof Module) {
                Set<String> imported = getIncludedModules(((Module) di).getName(), def);

                // collect the syntax from those modules
                CollectTerminalsVisitor ctv = new CollectTerminalsVisitor();
                // visit all modules to collect all Terminals first
                for (String modName : imported)
                    ctv.visitNode(def.getDefinitionContext().getModuleByName(modName));
                KSyntax2GrammarStatesFilter ks2gsf = new KSyntax2GrammarStatesFilter(ctv, ((Module) di).getModuleContext().getDeclaredSorts(), kem);
                for (String modName : imported)
                    ks2gsf.visitNode(def.getDefinitionContext().getModuleByName(modName));
                parsers.put(((Module) di).getName(), ks2gsf.getGrammar());
            }
        }
        return parsers;
    }

    /**
     * Recursively go through all the imports and find the list of all included modules.
     * @param modName    Name of the root module.
     * @param def        The Definition object in which to search for all the modules.
     * @return A set of all module names included by the given module name.
     */
    private static Set<String> getIncludedModules(String modName, Definition def) {
        Set<String> visited = new HashSet<>();
        getIncludedModules2(modName, def, visited);
        return visited;
    }

    private static void getIncludedModules2(String modName, Definition def, Set<String> visited) {
        if (visited.contains(modName))
            return;
        Module m = def.getDefinitionContext().getModuleByName(modName);
        visited.add(modName);
        for (ModuleItem mi : m.getItems()) {
            if (mi instanceof Import) {
                getIncludedModules2(((Import) mi).getName(), def, visited);
            }
        }
    }
}

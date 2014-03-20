package org.kframework.kil.loader;

import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.*;
import java.util.Collection;
import java.util.Set;


public class RemoveUnusedModules extends CopyOnWriteTransformer {

    private boolean autoinclude;
    public RemoveUnusedModules(Context context, boolean autoinclude) {
        super(RemoveUnusedModules.class.toString(), context);
        this.autoinclude = autoinclude;
    }

    @Override
    public ASTNode transform(Definition def) throws TransformerException {
        boolean change = false;
        Set<String> initialModules = new HashSet<>();
        if (autoinclude) {
            initialModules.add(Constants.AUTO_INCLUDED_MODULE);
            initialModules.add(Constants.AUTO_INCLUDED_SYNTAX_MODULE);
        }
        
        initialModules.add(def.getMainModule());
        CollectReachableModulesVisitor fm = new CollectReachableModulesVisitor(context, initialModules);
        def.accept(fm);
        ArrayList<DefinitionItem> reachableModulesList = new ArrayList<>();
        HashMap<String, Module> reachableModulesMap = fm.getResult();
//        System.out.println(reachableModulesMap.keySet());
        for (DefinitionItem definitionItem : def.getItems()) {
            if (definitionItem instanceof Module) {
                String name = ((Module) definitionItem).getName();
                if (!reachableModulesMap.containsKey(name)) {
//                    System.out.println(name);
                    change = true;
                    continue;
                }
            }
            reachableModulesList.add(definitionItem);
        }
        if (change) {
            def = def.shallowCopy();
            def.setItems(reachableModulesList);
            def.setModulesMap(reachableModulesMap);
        }
        return def;
    }

    private class CollectReachableModulesVisitor extends BasicVisitor  {
        HashMap<String,Module> included;
        private Collection<String> initialModules;

        public CollectReachableModulesVisitor(Context context, Collection<String> initialModules) {
            super(context);
            this.initialModules = initialModules;
            included = new HashMap<>();
        }

        @Override
        public void visit(Definition d) {
            Queue<Module> mods = new LinkedList<Module>();
            for (String name : initialModules) {
                Module mainModule = d.getModulesMap().get(name);
                mods.add(mainModule);
                included.put(name, mainModule);
            }
            //        System.out.println("push " + d.getMainModule());
            while (!mods.isEmpty()) {
                Module mod = mods.remove();
                //            System.out.println("pop " + mod.getName());
                if (null == mod.getItems()) continue;
                for(ModuleItem i : mod.getItems()) {
                    if (!(i instanceof Import)) continue;
                    String name = ((Import)i).getName();
                    if (included.containsKey(name)) continue;
                    Module mod1 = d.getModulesMap().get(name);
                    if (mod1!= null) {
                        mods.add(mod1);
                        included.put(name, mod1);
                    }
                }
            }
        }

        public HashMap<String, Module> getResult() {
            return included;
        }
    }

    @Override
    public String getName() {
        return "Flatten Modules";
    }
}

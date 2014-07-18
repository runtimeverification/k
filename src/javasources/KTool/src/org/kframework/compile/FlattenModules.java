// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;
import java.util.Set;


public class FlattenModules  extends BasicCompilerStep<Definition> {

    public FlattenModules(Context context) {
        super(context);
    }

    @Override
    public Definition compile(Definition def, String stepName) {
        FlattenModulesVisitor fm = new FlattenModulesVisitor(context);
        fm.visitNode(def);
        return fm.getResult();
    }

    private class FlattenModulesVisitor extends BasicVisitor  {
        public FlattenModulesVisitor(Context context) {
            super(context);
        }

        private final HashMap<String,Module> modules = new HashMap<>();
        private Definition result;

        @Override
        public Void visit(Definition d, Void _) {
            result = new Definition(d);
            Set<String> included = new HashSet<String>();
            Configuration cfg = null;
            super.visit(d, _);
            result.setFilename(d.getFilename());
            result.setLocation(d.getLocation());
            result.setMainFile(d.getMainFile());
            result.setMainModule(d.getMainModule());
            result.setMainSyntaxModule(d.getMainModule());
            result.setItems(new ArrayList<DefinitionItem>());
            Queue<Module> mods = new LinkedList<Module>();
            Module rmod = new Module();
            rmod.setName(d.getMainModule());
            rmod.setItems(new ArrayList<ModuleItem>());
            result.getItems().add(rmod);
            mods.add(modules.remove(d.getMainModule()));
            //        System.out.println("push " + d.getMainModule());
            while (!mods.isEmpty()) {
                Module mod = mods.remove();
                //            System.out.println("pop " + mod.getName());
                if (null == mod.getItems()) continue;
                for(ModuleItem i : mod.getItems()) {
                    if (i instanceof Import) {
                        String name = ((Import)i).getName();
                        if (included.contains(name)) continue;
                        if (!MetaK.isBuiltinModule(name)) {
                            if (modules.containsKey(name)) {
                                mods.add(modules.get(name));
                                included.add(name);
                            } else {
                                GlobalSettings.kem.register(new KException(ExceptionType.WARNING,
                                        KExceptionGroup.COMPILER,
                                        "Module " + name + " undefined.",
                                        getName(), i.getFilename(), i.getLocation()));
                            }
                            continue;
                        } else included.add(name);
                    }
                    if (i instanceof Configuration) {
                        if (null == cfg)
                            cfg = (Configuration)i;
                        continue;
                    }
                    rmod.getItems().add(i);
                }
            }
            if (null != cfg)
                rmod.getItems().add(cfg);
            return null;
        }

        @Override
        public Void visit(Module m, Void _) {
            modules.put(m.getName(), m);
            return null;
        }

        public Definition getResult() {
            return result;
        }
    }

    @Override
    public String getName() {
        return "Flatten Modules";
    }
}

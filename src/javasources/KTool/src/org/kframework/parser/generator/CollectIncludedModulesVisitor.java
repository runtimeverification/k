package org.kframework.parser.generator;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class CollectIncludedModulesVisitor extends BasicVisitor {
    public Set<String> modNames = new HashSet<String>();
    private String startModuleName;

    public CollectIncludedModulesVisitor(String startModuleName, Context context) {
        super(context);
        this.startModuleName = startModuleName;
    }

    public void visit(Definition def) {
        List<String> synQue = new LinkedList<String>();
        synQue.add(startModuleName);

        while (!synQue.isEmpty()) {
            String mname = synQue.remove(0);
            if (!modNames.contains(mname)) {
                modNames.add(mname);

                Module m = def.getModulesMap().get(mname);
                for (ModuleItem s : m.getItems()) {
                    if (s instanceof Import) {
                        Import imp = ((Import) s);
                        String mname2 = imp.getName();
                        Module mm = def.getModulesMap().get(mname2);
                        // if the module starts with # it means it is predefined in maude
                        if (!mname2.startsWith("#")) {
                            if (mm != null)
                                synQue.add(mm.getName());
                            else if (!MetaK.isKModule(mname2)) {
                                String msg = "Could not find module: " + mname2 + " imported from: " + m.getName();
                                GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.INNER_PARSER, msg, imp.getFilename(), imp.getLocation()));
                            }
                        }
                    }
                }
            }
        }
    }
}

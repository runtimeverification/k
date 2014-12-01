// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import java.util.Map.Entry;

import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.CollectIncludesVisitor;

public class AddAutoIncludedModulesVisitor extends BasicVisitor {

    public AddAutoIncludedModulesVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Definition def, Void _) {
        Import importMod = new Import(Constants.AUTO_INCLUDED_MODULE);

        for (DefinitionItem di : def.getItems()) {
            if (di instanceof Module) {
                Module m = (Module) di;
                if (!m.isPredefined()) {
                    CollectIncludesVisitor getIncludes = new CollectIncludesVisitor(context);
                    getIncludes.visitNode(m);
                    if (!getIncludes.getImportList().contains(importMod))
                        m.getItems().add(0, importMod);
                }
            }
        }
        return null;
    }
}

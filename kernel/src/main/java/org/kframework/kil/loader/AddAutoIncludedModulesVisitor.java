// Copyright (c) 2012-2015 K Team. All Rights Reserved.
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
    public Void visit(Definition def, Void _void) {
        for (DefinitionItem di : def.getItems()) {
            if (di instanceof Module) {
                Module m = (Module) di;
                if (!m.isPredefined()) {
                    CollectIncludesVisitor getIncludes = new CollectIncludesVisitor(context);
                    getIncludes.visitNode(m);
                    Import importMod = new Import(Constants.AUTO_INCLUDED_MODULE);
                    // if there is a separate module syntax, add only the special module for syntactic stuff
                    if (m.getName().equals(def.getMainSyntaxModule()) && !def.getMainSyntaxModule().equals(def.getMainModule()))
                        importMod = new Import(Constants.AUTO_INCLUDED_SYNTAX_MODULE);

                    if (!getIncludes.getImportList().contains(importMod))
                        m.getItems().add(0, importMod);
                }
            }
        }
        return null;
    }
}

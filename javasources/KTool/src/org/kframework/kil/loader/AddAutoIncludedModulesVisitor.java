package org.kframework.kil.loader;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.CollectIncludedModulesVisitor;
import org.kframework.parser.generator.CollectIncludesVisitor;

public class AddAutoIncludedModulesVisitor extends BasicVisitor {

	@Override
	public void visit(Definition def) {
		Set<String> synModules = new HashSet<String>();
		Import importSyn = new Import("AUTO-INCLUDED-MODULE-SYNTAX");
		Import importMod = new Import("AUTO-INCLUDED-MODULE");

		if (!def.getMainSyntaxModule().equals(def.getMainModule())) {
			CollectIncludedModulesVisitor inclviz = new CollectIncludedModulesVisitor(def.getMainSyntaxModule());
			def.accept(inclviz);
			synModules = inclviz.synModNames;

			for (String modName : synModules) {
				Module m = def.getModulesMap().get(modName);
				if (m != null && !m.isPredefined()) {
					CollectIncludesVisitor getIncludes = new CollectIncludesVisitor();
					m.accept(getIncludes);
					if (!getIncludes.getImportList().contains(importSyn))
						m.getItems().add(0, importSyn);
				}
			}
		}

		CollectIncludedModulesVisitor inclviz = new CollectIncludedModulesVisitor(def.getMainModule());
		def.accept(inclviz);

		for (String modName : inclviz.synModNames) {
			if (!synModules.contains(modName)) {
				Module m = def.getModulesMap().get(modName);
				if (m != null && !m.isPredefined()) {
					CollectIncludesVisitor getIncludes = new CollectIncludesVisitor();
					m.accept(getIncludes);
					if (!getIncludes.getImportList().contains(importMod))
						m.getItems().add(0, importMod);
				}
			}
		}
	}
}

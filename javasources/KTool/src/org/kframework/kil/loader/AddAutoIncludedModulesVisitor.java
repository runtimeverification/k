package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.parser.generator.CollectIncludedModulesVisitor;
import org.kframework.parser.generator.CollectIncludesVisitor;

public class AddAutoIncludedModulesVisitor extends BasicVisitor {

	@Override
	public void visit(Definition def) {
		Import importMod = new Import("AUTO-INCLUDED-MODULE");

		CollectIncludedModulesVisitor inclviz = new CollectIncludedModulesVisitor(def.getMainModule());
		def.accept(inclviz);

		for (String modName : inclviz.modNames) {
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

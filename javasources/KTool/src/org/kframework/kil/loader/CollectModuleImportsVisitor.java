package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectModuleImportsVisitor extends BasicVisitor {

	private String parentModule = null;

	public void visit(Definition def) {
		super.visit(def);
		DefinitionHelper.finalizeModules();
	}

	public void visit(Module m) {
		parentModule = m.getName();
		super.visit(m);
	}

	public void visit(Import i) {
		DefinitionHelper.addModuleImport(parentModule, i.getName());
	}
}

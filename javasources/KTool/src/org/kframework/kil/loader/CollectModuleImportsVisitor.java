package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectModuleImportsVisitor extends BasicVisitor {

	public CollectModuleImportsVisitor(DefinitionHelper definitionHelper) {
		super(definitionHelper);
	}

	private String parentModule = null;

	public void visit(Definition def) {
		super.visit(def);
		definitionHelper.finalizeModules();
	}

	public void visit(Module m) {
		parentModule = m.getName();
		super.visit(m);
	}

	public void visit(Import i) {
		definitionHelper.addModuleImport(parentModule, i.getName());
	}
}

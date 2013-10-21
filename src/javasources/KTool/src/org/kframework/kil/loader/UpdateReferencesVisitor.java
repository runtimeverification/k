package org.kframework.kil.loader;

import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;

public class UpdateReferencesVisitor extends BasicVisitor {
	public UpdateReferencesVisitor(Context context) {
		super(context);
	}

	private String prodSort;
	private String moduleName;

	@Override
	public void visit(Module mod) {
		moduleName = mod.getName();
		super.visit(mod);
	}

	/**
	 * Add the sort attribute to every production when calling the collector
	 */
	@Override
	public void visit(Syntax syn) {
		context.definedSorts.add(syn.getSort().getName());
		prodSort = syn.getSort().getName();
		super.visit(syn);
	}

	@Override
	public void visit(Production node) {
		node.setSort(prodSort);
		node.setOwnerModuleName(moduleName);
	}
}

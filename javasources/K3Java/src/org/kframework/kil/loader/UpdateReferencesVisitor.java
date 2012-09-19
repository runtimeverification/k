package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;

public class UpdateReferencesVisitor extends BasicVisitor {
	private String prodSort;

	/**
	 * Add the sort attribute to every production when calling the collector
	 */
	@Override
	public void visit(Syntax syn) {
		prodSort = syn.getSort().getName();
		super.visit(syn);
	}

	@Override
	public void visit(Production node) {
		node.setSort(prodSort);
	}
}

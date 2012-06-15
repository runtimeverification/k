package ro.uaic.info.fmse.loader;

import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class UpdateReferencesVisitor extends BasicVisitor {
	private String prodSort;

	/**
	 * Add the sort attribute to every production when calling the collector
	 */
	@Override
	public void visit(Syntax syn) {
		prodSort = syn.getSort().getSort();
		super.visit(syn);
	}

	@Override
	public void visit(Production node) {
		node.setSort(prodSort);
	}
}

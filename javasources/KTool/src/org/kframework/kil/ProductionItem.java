package org.kframework.kil;

public abstract class ProductionItem extends ASTNode {
	public ProductionItem() {
		super();
	}

	public ProductionItem(ProductionItem sort) {
		super(sort);
	}
}

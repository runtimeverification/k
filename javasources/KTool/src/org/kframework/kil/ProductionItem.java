package org.kframework.kil;

public abstract class ProductionItem extends ASTNode {
	public ProductionItem() {
		super();
	}

	public ProductionItem(ProductionItem sort) {
		super(sort);
	}

	public enum ProductionType {
		TERMINAL, SORT, USERLIST, LEXICAL
	}

	public abstract ProductionType getType();
}

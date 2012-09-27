package org.kframework.kil;

import org.w3c.dom.Element;

public abstract class ProductionItem extends ASTNode {
	public ProductionItem(Element element) {
		super(element);
	}

	public ProductionItem() {
		super();
	}

	public ProductionItem(ProductionItem sort) {
		super(sort);
	}

	public enum ProductionType {
		TERMINAL, SORT, USERLIST
	}

	public abstract ProductionType getType();
}

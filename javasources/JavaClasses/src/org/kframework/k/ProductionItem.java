package org.kframework.k;

import org.w3c.dom.Element;


public abstract class ProductionItem extends ASTNode {
	public ProductionItem(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	public ProductionItem(){
		super();
	}
	
	public ProductionItem(ProductionItem sort) {
		super(sort);
	}

	public enum ProductionType { TERMINAL, SORT, USERLIST } ;
	
	public ProductionType getType() {
		return null;
	}
}

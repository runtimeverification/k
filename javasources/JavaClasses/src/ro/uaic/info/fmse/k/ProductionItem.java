package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.ASTNode;

public abstract class ProductionItem extends ASTNode {
	public ProductionItem(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	public enum ProductionType { TERMINAL, SORT, USERLIST } ;
	
	public ProductionType getType() {
		return null;
	}
}

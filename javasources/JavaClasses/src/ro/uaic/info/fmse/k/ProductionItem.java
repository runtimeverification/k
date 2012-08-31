package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;


public abstract class ProductionItem extends ASTNode {
	public ProductionItem(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	public ProductionItem(){
		super("generated", "generated");
	}
	
	public enum ProductionType { TERMINAL, SORT, USERLIST } ;
	
	public ProductionType getType() {
		return null;
	}
}

package org.kframework.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;


public abstract class DefinitionItem extends ASTNode {
	
	public DefinitionItem() {
		super("File System", "generated");
	}
	
	public DefinitionItem(DefinitionItem di) {
		super(di);
	}

	public DefinitionItem(Element element) {
		super(element);
	}
	
	@Override
	public Element toXml(Document doc) {
		// TODO Auto-generated method stub
		return null;
	}
}

package org.kframework.kil;

import org.w3c.dom.Element;

public abstract class DefinitionItem extends ASTNode {

	protected boolean predefined;

	public DefinitionItem() {
		super("File System", "generated");
	}

	public DefinitionItem(DefinitionItem di) {
		super(di);
	}

	public DefinitionItem(Element element) {
		super(element);
	}

	public void setPredefined(boolean predefined) {
		this.predefined = predefined;
	}

	public boolean isPredefined() {
		return predefined;
	}
}

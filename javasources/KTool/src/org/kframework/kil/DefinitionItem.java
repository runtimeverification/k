package org.kframework.kil;

import org.w3c.dom.Element;

public abstract class DefinitionItem extends ASTNode {

	/** set iff the item was read from a file in the standard libraries */
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

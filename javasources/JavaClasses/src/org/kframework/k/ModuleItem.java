package org.kframework.k;

import org.w3c.dom.Element;

public abstract class ModuleItem extends ASTNode {
	public ModuleItem(String location, String filename) {
		super(location, filename);
	}

	public ModuleItem(Element element) {
		super(element);
	}

	public ModuleItem(ModuleItem s) {
		super(s);
	}

	public ModuleItem() {
		super("generated", "generated");
	}

	public java.util.List<String> getLabels() {
		return null;
	}

	public java.util.List<String> getAllSorts() {
		return null;
	}
}

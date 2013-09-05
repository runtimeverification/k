package org.kframework.kil;

import org.w3c.dom.Element;

import aterm.ATermAppl;

public abstract class ModuleItem extends ASTNode {
	public ModuleItem(Element element) {
		super(element);
	}

	public ModuleItem(ATermAppl element) {
		super(element);
	}

	public ModuleItem(ModuleItem s) {
		super(s);
	}

	public ModuleItem() {
		super();
	}

	public java.util.List<String> getLabels() {
		return null;
	}

	public java.util.List<String> getKLabels() {
		return null;
	}

	public java.util.List<String> getAllSorts() {
		return null;
	}
}

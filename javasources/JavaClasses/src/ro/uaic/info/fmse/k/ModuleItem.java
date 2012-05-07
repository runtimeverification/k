package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.ASTNode;

public abstract class ModuleItem extends ASTNode {

	public ModuleItem(Element element) {
		super(element);
	}

	public java.util.List<String> getLabels() {
		return null;
	}

	public java.util.List<String> getAllSorts() {
		return null;
	}
}

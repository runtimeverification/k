package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.loader.Constants;
import org.kframework.visitors.Modifier;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Document;
import org.w3c.dom.Element;


public class Import extends ModuleItem {

	String name;

	public Import(Element element) {
		super(element);
		name = element.getAttribute(Constants.NAME_name_ATTR);
	}

	public Import(String importName) {
		super((Element) null);
		name = importName;
	}

	public Import(Import import1) {
		super(import1);
		this.name = import1.name; 
	}

	@Override
	public String toString() {
		return "  imports " + name;
	}

	@Override
	public String toMaude() {
		return "including " + name + " .";
	}

	@Override
	public Element toXml(Document doc) {
		Element import_ = doc.createElement(Constants.IMPORT);
		import_.setTextContent(name);
		return import_;
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	@Override
	public Import shallowCopy() {
		return new Import(this);
	}
}

package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


public class Set extends Collection {

	public Set(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	public Set(Set node) {
		super(node);
	}

	public Set(String location, String filename) {
		super(location, filename, "Set");
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	@Override
	public Set shallowCopy() {
		return new Set(this);
	}
}

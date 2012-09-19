package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Element;


public class Map extends Collection {

	public Map(Element element) {
		super(element);
	}

	public Map(String location, String filename) {
		super(location, filename, "Map");
	}

	public Map(Map node) {
		super(node);
	}

	public Map() {
		super("Map");
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
	public Map shallowCopy() {
		return new Map(this);
	}
}

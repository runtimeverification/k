package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
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

package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Element;


public class Bag extends Collection {
	public Bag(String location, String filename) {
		super(location, filename, "Bag");
	}

	public Bag(Element element) {
		super(element);
	}

	public Bag(Bag node) {
		super(node);
	}

	public Bag() {
		super("Bag");
	}

	@Override
	public String toString() {
		return super.toString();
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException  {
		return visitor.transform(this);
	}
	
	@Override
	public Bag shallowCopy() {
		return new Bag(this);
	}
}
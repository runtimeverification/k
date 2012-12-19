package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

public class FreezerHole extends Term {
	private int index;
	
	public FreezerHole(int index) {
		super("K");
		this.index = index;
	}
	
	public FreezerHole(Element element) {
		// TODO: for Radu
		super(element);
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
	public Term shallowCopy() {
		return new FreezerHole(this.index);
	}
	
	public int getIndex() {
		return index;
	}
}

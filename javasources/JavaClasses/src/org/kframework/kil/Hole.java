package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


public class Hole extends Term {
	public Hole(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
	}

	public Hole(Hole hole) {
		super(hole);
	}

	public String toString() {
		return "[]:" + sort + " ";
	}

	@Override
	public String toMaude() {
		return "HOLE";
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

	@Override
	public Hole shallowCopy() {
		return new Hole(this);
	}
}
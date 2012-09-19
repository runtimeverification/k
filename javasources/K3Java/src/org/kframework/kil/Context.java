package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

public class Context extends Sentence {

	public Context(Element element) {
		super(element);
	}

	public Context(Context node) {
		super(node);
	}

	public String toString() {
		String content = "  context ";
		content += this.body + " ";

		return content + attributes.toString();
	}

	@Override
	public String toMaude() {
		return "mb context " + super.toMaude();
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
	public Context shallowCopy() {
		return new Context(this);
	}
}

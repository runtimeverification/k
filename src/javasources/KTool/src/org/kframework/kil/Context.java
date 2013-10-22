package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

/**
 * A context declaration.
 * The context is represented as a term, with the focused point
 * indicated by one occurence of either {@link Hole} or a {@link Rewrite} whose
 * left hand side is {@link Hole}.
 */
public class Context extends Sentence {

	public Context(Element element) {
		super(element);
	}

	public Context(Context node) {
		super(node);
	}

	public Context() {
		super();
	}

	public Context(Sentence term) {
		super(term);
	}

	public String toString() {
		String content = "  context ";
		content += this.body + " ";

		return content + attributes;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public Context shallowCopy() {
		return new Context(this);
	}
}

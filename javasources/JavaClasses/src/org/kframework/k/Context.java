package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.loader.Constants;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Document;
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
	public Element toXml(Document doc) {
		Element context = doc.createElement(Constants.CONTEXT);
		context.setTextContent("notimplementedyet");
		return context;
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

package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

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
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
	
	@Override
	public Context shallowCopy() {
		return new Context(this);
	}
}

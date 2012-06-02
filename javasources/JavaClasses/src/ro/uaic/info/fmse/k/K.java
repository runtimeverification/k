package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;


public class K extends Collection {

	public K(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}
	public K(K node) {
		super(node);
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
}

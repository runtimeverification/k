package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Visitor;


public class K extends Collection {

	public K(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

}

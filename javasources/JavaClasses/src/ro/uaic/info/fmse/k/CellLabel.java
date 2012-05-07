package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Visitor;

public class CellLabel extends Term {
	public CellLabel(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	String name;

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}

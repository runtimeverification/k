package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Visitor;

public class KInjectedLabel extends KLabel {
	public KInjectedLabel(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	Term thing;

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		thing.accept(visitor);
	}
}

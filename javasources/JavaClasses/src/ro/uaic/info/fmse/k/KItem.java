package ro.uaic.info.fmse.k;

import java.util.List;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Visitor;

public class KItem extends Term {
	public KItem(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	Term label;
	List<Term> terms;

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		label.accept(visitor);
		for (Term di : terms)
			di.accept(visitor);
	}
}

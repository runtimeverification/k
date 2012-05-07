package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Visitor;

public class ComposedTerm extends Term {
	public ComposedTerm(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	String constructor;
	java.util.List<Term> terms;
	String sort;

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		for (Term di : terms)
			di.accept(visitor);
	}
}

package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;


public class ComposedTerm extends Term{
	public ComposedTerm(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}
	String constructor;
	java.util.List<Term> terms;
	String sort;
	
}

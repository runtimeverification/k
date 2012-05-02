package ro.uaic.info.fmse.k;

import java.util.List;

import org.w3c.dom.Element;

public class KItem extends Term {
	public KItem(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}
	Term label;
	List<Term> terms;
}

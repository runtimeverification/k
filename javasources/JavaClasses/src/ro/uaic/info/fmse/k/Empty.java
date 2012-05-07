package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.Visitor;

public class Empty extends Term {
	String sort;

	public Empty(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
	}

	public String toString() {
		return "." + sort + " ";
	}

	@Override
	public String toMaude() {
		return ".";
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}

package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;

public class Variable extends Term {
	String name;
	String sort;

	public Variable(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.name = element.getAttribute(Constants.NAME_name_ATTR);
	}

	public String toString() {
		return name + ":" + sort + " ";
	}
}
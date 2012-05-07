package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;

public class Empty extends Term {
	String sort;

	public Empty(String location, String filename, String sort) {
		super(location, filename);
		this.sort = sort;
	}
	
	public Empty(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
	}

	public String toString() {
		return "." + sort + " ";
	}

	@Override
	public String toMaude() {
		if (MaudeHelper.basicSorts.contains(sort))
			return "(.)." + sort;
		
		return "." + sort;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}

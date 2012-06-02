package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;

public abstract class Term extends ASTNode {
	String sort;

	public Term(Term t) {
		super(t);
		this.sort = t.sort;
	}
	
	public Term(String location, String filename, String sort) {
		super(location, filename);
		setSort(sort);
	}

	public Term(String location, String filename) {
		super(location, filename);
	}

	public Term(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
	}

	@Override
	public Element toXml(Document doc) {
		Element term = doc.createElement(Constants.TERM);
		return term;
	}

	public String getSort() {
		return sort;
	}

	private void setSort(String sort) {
		this.sort = sort;
	}
}

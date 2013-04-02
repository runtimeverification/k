package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.matchers.Matchable;

import org.w3c.dom.Element;


/**
 * Base of all nodes that represent terms in the semantics.
 * Each term is labeled with a sort.
 */
public abstract class Term extends ASTNode implements Matchable {
	protected String sort;

    protected Term(){}

	public Term(Term t) {
		super(t);
		this.sort = t.sort;
	}
	
	public Term(String location, String filename, String sort) {
		super(location, filename);
		setSort(sort);
	}

	public Term(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
	}

	public Term(String sort) {
		super();
		this.sort = sort;
	}

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}
	
	@Override
	public abstract Term shallowCopy();

}

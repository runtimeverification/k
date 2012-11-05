package org.kframework.kil;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

public abstract class Collection extends Term {

	protected java.util.List<Term> contents;
	
	public Collection(String sort) {
		super(sort);
		contents = new ArrayList<Term>();
	}

	public Collection(Collection c) {
		super(c);
		this.contents = c.contents;
	}

	public Collection(String location, String filename, String sort) {
		super(location, filename, sort);
		contents = new ArrayList<Term>();
	}

	public Collection(Element element) {
		super(element);

		contents = new ArrayList<Term>();
		List<Element> children = XML.getChildrenElements(element);
		for (Element e : children)
			contents.add((Term) JavaClassesFactory.getTerm(e));
	}

	public Collection(String sort, List<Term> col) {
		super(sort);
		this.contents = col;
	}

	@Override
	public String toString() {
		String content = "";
		for (Term t : contents)
			content += t;
		return content;
	}

	public java.util.List<Term> getContents() {
		return contents;
	}

	public void setContents(java.util.List<Term> contents) {
		this.contents = contents;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		for (int i = 0; i < this.contents.size(); i++) {
			Term elem = (Term) visitor.modify(this.contents.get(i));
			this.contents.set(i, elem);
		}
	}
	
	@Override
	public abstract Collection shallowCopy();
}

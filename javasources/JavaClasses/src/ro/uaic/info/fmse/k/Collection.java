package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public abstract class Collection extends Term {

	protected java.util.List<Term> contents;

	public Collection(String location, String filename, java.util.List<Term> contents) {
		super(location, filename);
		this.contents = new ArrayList<Term>();
		this.contents.addAll(contents);
	}

	public Collection(Element element) {
		super(element);

		contents = new LinkedList<Term>();
		List<Element> children = XML.getChildrenElements(element);
		for (Element e : children)
			contents.add((Term) JavaClassesFactory.getTerm(e));
	}

	@Override
	public String toString() {
		String content = "";
		for (Term t : contents)
			content += t;
		return content;
	}

	@Override
	public String toMaude() {
		String content = "";

		for (Term term : contents)
			if (term != null)
				content += term.toMaude() + ",";

		if (content.length() > 1)
			content = content.substring(0, content.length() - 1);

		return "__(" + content + ")";
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		for (Term di : contents)
			di.accept(visitor);
	}
}

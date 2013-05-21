package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/** Represents parentheses uses for grouping. All productions labeled bracket parse to this. */
public class Bracket extends Term {

	private Term content;

	public Term getContent() {
		return content;
	}

	public void setContent(Term content) {
		this.content = content;
	}

	public String getSort() {
		if (content instanceof Ambiguity)
			return super.getSort();
		return content.getSort();
	}

	public Bracket(Bracket i) {
		super(i);
		this.content = i.content;
	}

	public Bracket(Term t, Context context) {
		super(t.getSort());
		this.content = t;
	}

	public Bracket(String location, String filename, String sort) {
		super(location, filename, sort);
	}

	public Bracket(String location, String filename, Term t, Context context) {
		super(location, filename, t.getSort());
		this.content = t;
	}

	public Bracket(Element element) {
		super(element);
		this.content = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public Bracket(ATermAppl atm) {
		super(atm);
		this.sort = StringUtil.getSortNameFromCons(atm.getName());

		content = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));
	}

	public Bracket(String sort) {
		super(sort);
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public void accept(Matcher matcher, Term toMatch) {
		matcher.match(this, toMatch);
	}

	@Override
	public Bracket shallowCopy() {
		return new Bracket(this);
	}

	@Override
	public String toString() {
		return "(" + content + ")";
	}

	@Override
	public int hashCode() {
		return content.hashCode();
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Bracket))
			return false;
		Bracket b = (Bracket) o;
		return content.equals(b.content);
	}

	@Override
	public boolean contains(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Bracket))
			return false;
		Bracket b = (Bracket) o;
		return content.contains(b.content);
	}

}

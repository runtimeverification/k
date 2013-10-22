package org.kframework.kil;

import org.kframework.kil.loader.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/** Represents parentheses uses for grouping. All productions labeled bracket parse to this. */
public class Cast extends Term {

	private Term content;
	private boolean syntactic = true;

	public Term getContent() {
		return content;
	}

	public void setContent(Term content) {
		this.content = content;
	}

	public Cast(Cast i) {
		super(i);
		this.content = i.content;
		this.syntactic = i.syntactic;
	}

	public Cast(Term t, Context context) {
		super(t.getSort());
		this.content = t;
	}

	public Cast(ATermAppl atm) {
		super(atm);
		this.sort = StringUtil.getSortNameFromCons(atm.getName());
		if (atm.getName().endsWith("1Cast"))
			this.syntactic = false;
		else
			this.syntactic = true;

		content = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));
	}

	public Cast(String location, String filename, String sort) {
		super(location, filename, sort);
	}

	public Cast(String location, String filename, Term t, org.kframework.kil.loader.Context context) {
		super(location, filename, t.getSort());
		this.content = t;
	}

	public Cast(Element element) {
		super(element);
		if (element.getAttribute("syntactic").equals("true"))
			this.syntactic = true;
		else
			this.syntactic = false;
		this.content = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public Cast(String sort) {
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
	public Cast shallowCopy() {
		return new Cast(this);
	}

	@Override
	public String toString() {
		return "(" + content + ")";
	}

	public void setSyntactic(boolean syntactic) {
		this.syntactic = syntactic;
	}

	public boolean isSyntactic() {
		return syntactic;
	}

	@Override
	public int hashCode() {
		return content.hashCode() + (this.syntactic ? 1 : 0);
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Cast))
			return false;
		Cast c = (Cast) o;
		return this.syntactic == c.syntactic && this.content.equals(c.content);
	}

	@Override
	public boolean contains(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Cast))
			return false;
		Cast c = (Cast) o;
		return this.syntactic == c.syntactic && this.content.contains(c.content);
	}
}

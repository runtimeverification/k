package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

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

	public Cast(Term t) {
		super(t.getSort());
		this.content = t;
	}

	public Cast(String location, String filename, String sort) {
		super(location, filename, sort);
	}

	public Cast(Element element) {
		super(element);
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
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
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
}

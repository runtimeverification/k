package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

public class SetItem extends CollectionItem {

	public SetItem(Element element) {
		super(element);
		this.value = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public SetItem(ATermAppl atm) {
		super(atm);
		value = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));
	}

	public SetItem(SetItem node) {
		super(node);
	}

	public SetItem(Term node) {
		super("SetItem");
		this.value = node;
	}

	public String toString() {
		return this.value.toString();
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
	public SetItem shallowCopy() {
		return new SetItem(this);
	}
}

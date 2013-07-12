package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import aterm.ATermAppl;

public class BagItem extends CollectionItem {
	public BagItem(String location, String filename) {
		super(location, filename, "BagItem");
	}

	public BagItem(Element element) {
		super(element);
		this.value = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public BagItem(ATermAppl atm) {
		super(atm);
		value = (Term) JavaClassesFactory.getTerm(atm.getArgument(0));
	}

	public BagItem(BagItem node) {
		super(node);
	}

	public BagItem(Term node) {
		super("BagItem");
		this.value = node;
	}

	public String toString() {
		return this.value.toString();
	}

	public Term getItem() {
		return value;
	}

	public void setItem(Term item) {
		this.value = item;
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
	public BagItem shallowCopy() {
		return new BagItem(this);
	}
}

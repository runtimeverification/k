package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.loader.JavaClassesFactory;
import org.kframework.visitors.Modifier;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.utils.xml.XML;

public class ListItem extends CollectionItem {
	public ListItem(Element element) {
		super(element);
		this.value = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public ListItem(ListItem node) {
		super(node);
	}

	public String toString() {
		return this.value.toString();
	}

	@Override
	public String toMaude() {
		return "ListItem(" + value.toMaude() + ")";
	}

	@Override
	public void applyToAll(Modifier visitor) {
		value = (Term) visitor.modify(value);
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
	public ListItem shallowCopy() {
		return new ListItem(this);
	}
}

package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.utils.xml.XML;

public class BagItem extends CollectionItem {
	public BagItem(String location, String filename) {
		super(location, filename, "BagItem");
	}

	public BagItem(Element element) {
		super(element);
		this.value = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public BagItem(BagItem node) {
		super(node);
	}

	public String toString() {
		return this.value.toString();
	}

	@Override
	public String toMaude() {
		return "BagItem(" + value.toMaude() + ")";
	}

	public Term getItem() {
		return value;
	}

	public void setItem(Term item) {
		this.value = item;
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
	public ASTNode accept(Transformer visitor) throws TransformerException  {
		return visitor.transform(this);
	}
	
	@Override
	public BagItem shallowCopy() {
		return new BagItem(this);
	}
}

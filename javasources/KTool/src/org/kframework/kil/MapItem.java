package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.utils.xml.XML;
import org.w3c.dom.Element;


public class MapItem extends CollectionItem {
	private Term key;

	public MapItem(Element element) {
		super(element);
		Element elm = XML.getChildrenElementsByTagName(element, Constants.KEY).get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.key = (Term) JavaClassesFactory.getTerm(elmBody);

		elm = XML.getChildrenElementsByTagName(element, Constants.VALUE).get(0);
		elmBody = XML.getChildrenElements(elm).get(0);
		this.value = (Term) JavaClassesFactory.getTerm(elmBody);
	}

	public MapItem(String location, String filename) {
		super(location, filename, "MapItem");
	}
	
	public MapItem(MapItem node) {
		super(node);
		this.key = node.key;
	}

	public MapItem() {
		super("MapItem");
	}

	public void setKey(Term key) {
		this.key = key;
	}

	public Term getKey() {
		return key;
	}

	public Term getValue() {
		return value;
	}

	public void setValue(Term t) {
		value = t;
	}

	public String toString() {
		return this.key + " |->" + this.value;
	}

	@Override
	public String toMaude() {
		return "_|->_(" + key.toMaude() + "," + value.toMaude() + ")";
	}

	@Override
	public void applyToAll(Modifier visitor) {
		key = (Term) visitor.modify(key);
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
	public MapItem shallowCopy() {
		return new MapItem(this);
	}
}

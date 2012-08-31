package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

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
		super(location, filename);
	}
	
	public MapItem(MapItem node) {
		super(node);
		this.key = node.key;
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
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
}

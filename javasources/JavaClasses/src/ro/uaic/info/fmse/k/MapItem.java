package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class MapItem extends Term {
	Term key;
	Term value;

	public MapItem(Element element) {
		super(element);
		Element elm = XML.getChildrenElementsByTagName(element, Constants.KEY).get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.key = (Term) JavaClassesFactory.getTerm(elmBody);

		elm = XML.getChildrenElementsByTagName(element, Constants.VALUE).get(0);
		elmBody = XML.getChildrenElements(elm).get(0);
		this.value = (Term) JavaClassesFactory.getTerm(elmBody);
	}

	public String toString() {
		return this.key + " |->" + this.value;
	}

	@Override
	public String toMaude() {
		return "_|->_(" + key.toMaude() + "," + value.toMaude() + ")";
	}

	@Override
	public void all(Visitor visitor) {
		key = (Term) visitor.visit(key);
		value = (Term) visitor.visit(value);
	}
}

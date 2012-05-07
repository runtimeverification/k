package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class SetItem extends Term {
	Term item;

	public SetItem(Element element) {
		super(element);
		this.item = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(
				element).get(0));
	}

	public String toString() {
		return this.item.toString();
	}

	@Override
	public String toMaude() {
		return "SetItem(" + item.toMaude() + ")";
	}

	public void accept(Visitor visitor) {
		visitor.visit(this);
		item.accept(visitor);
	}
}

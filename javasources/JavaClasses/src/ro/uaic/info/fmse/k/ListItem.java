package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class ListItem extends Term {
	Term item;

	public ListItem(Element element) {
		super(element);
		this.item = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(
				element).get(0));
	}

	public String toString() {
		return this.item.toString();
	}

	@Override
	public String toMaude() {
		return "ListItem(" + item.toMaude() + ")";
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		item.accept(visitor);
	}
}

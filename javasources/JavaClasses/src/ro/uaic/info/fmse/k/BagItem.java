package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class BagItem extends Term {
	Term item;

	public BagItem(String location, String filename) {
		super(location, filename);
	}

	public BagItem(Element element) {
		super(element);
		this.item = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));
	}

	public String toString() {
		return this.item.toString();
	}

	@Override
	public String toMaude() {
		return "BagItem(" + item.toMaude() + ")";
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		item.accept(visitor);
	}

	public Term getItem() {
		return item;
	}

	public void setItem(Term item) {
		this.item = item;
	}

	@Override
	public void all(Visitor visitor) {
		item = (Term) visitor.visit(item);
	}
}

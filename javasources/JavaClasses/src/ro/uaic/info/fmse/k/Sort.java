package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.Visitor;

public class Sort extends ProductionItem {

	String sort;

	public Sort(Element element) {
		super(element);

		sort = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public ProductionType getType() {
		return ProductionType.SORT;
	}

	@Override
	public String toString() {
		return sort;
	}

	@Override
	public String toMaude() {
		return sort;
	}

	@Override
	public Element toXml(Document doc) {
		// TODO Auto-generated method stub
		Element sort = doc.createElement(Constants.SORT);
		sort.setTextContent(this.sort);

		return sort;
	}

	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public void all(Visitor visitor) {
	}
}

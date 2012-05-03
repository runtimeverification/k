package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;

public class Terminal extends Term implements ProductionItem {

	String terminal;

	public Terminal(Element element) {
		super(element);
		terminal = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	@Override
	public String toString() {
		return "\"" + terminal + "\"";
	}
	
	@Override
	public String toMaude() {
		return "";
	}
}

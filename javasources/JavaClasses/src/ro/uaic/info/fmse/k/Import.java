package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;


public class Import extends ModuleItem {

	String name;
	public Import(Element element) {
		super(element);
		name = element.getAttribute(Constants.NAME_name_ATTR);
	}
	
	@Override
	public String toString() {
		return "  imports " + name;
	}
	
	@Override
	public String toMaude() {
		return "including " + name;
	}

	@Override
	public Element toXml(Document doc) {
		Element import_ = doc.createElement(Constants.IMPORT);
		import_.setTextContent(name);
		return import_;
	}
}

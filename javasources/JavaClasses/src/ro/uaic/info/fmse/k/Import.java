package ro.uaic.info.fmse.k;

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
		return "imports " + name;
	}
}

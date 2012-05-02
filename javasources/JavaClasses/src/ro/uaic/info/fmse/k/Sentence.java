package ro.uaic.info.fmse.k;

import java.util.Map;

import org.w3c.dom.Element;

public abstract class Sentence extends ModuleItem {
	public Sentence(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}
	Term body;
	Term condition = null;
	Map<String, String> attributes;

}

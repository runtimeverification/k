package ro.uaic.info.fmse.k;

import java.util.HashMap;
import java.util.Map.Entry;
import org.w3c.dom.Element;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;

public class Context extends Sentence {

	public Context(Element element) {
		super(element);
		this.body = (Term) JavaClassesFactory.getTerm(XML.getChildrenElementsByTagName(element, Constants.BODY).get(0));

		java.util.List<Element> its = XML.getChildrenElementsByTagName(element, Constants.COND);
		if (its.size() > 0)
			this.condition = (Term) JavaClassesFactory.getTerm(its.get(0));

		attributes = new HashMap<String, String>();
		its = XML.getChildrenElementsByTagName(element, Constants.ATTRIBUTES);
		// assumption: <attributes> appears only once
		if (its.size() > 0) {
			its = XML.getChildrenElements(its.get(0));
			for (Element e : its) {
				attributes.put(e.getAttribute(Constants.KEY_key_ATTR), e.getAttribute(Constants.VALUE_value_ATTR));
			}
		}
	}

	public String toString() {
		String content = "context ";
		content += this.body + " ";

		String attributes = "";
		for (Entry<String, String> entry : this.attributes.entrySet()) {
			String value = entry.getValue();
			if (!value.equals(""))
				value = "(" + value + ")";

			attributes += " " + entry.getKey() + value;
		}
		return content + "[" + attributes + "]";
	}
}

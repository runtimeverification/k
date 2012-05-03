package ro.uaic.info.fmse.k;

import java.util.HashMap;
import java.util.Map.Entry;
import org.w3c.dom.Element;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;

public class Rule extends Sentence {
	private String label;

	public Rule(Element element) {
		super(element);
		Element elm = XML.getChildrenElementsByTagName(element, Constants.BODY).get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.body = (Term) JavaClassesFactory.getTerm(elmBody);
		setLabel(element.getAttribute(Constants.LABEL));

		java.util.List<Element> its = XML.getChildrenElementsByTagName(element, Constants.COND);
		if (its.size() > 0)
			this.condition = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(its.get(0)).get(0));

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

	public void setLabel(String label) {
		this.label = label;
	}

	public String getLabel() {
		return label;
	}

	public String toString() {
		String content = "  rule ";

		if (this.label != null && !this.label.equals(""))
			content += "[" + this.label + "]: ";

		content += this.body + " ";

		String attributes = "";
		if (!this.attributes.isEmpty()) {
			attributes += "[";
			for (Entry<String, String> entry : this.attributes.entrySet()) {
				String value = entry.getValue();
				if (!value.equals(""))
					value = "(" + value + ")";

				attributes += " " + entry.getKey() + value;
			}
			attributes += "]";
		}
		return content + attributes;
	}
}

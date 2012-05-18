package ro.uaic.info.fmse.k;

import java.util.HashMap;
import java.util.Map.Entry;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class Context extends Sentence {

	public Context(Element element) {
		super(element);
		Element elm = XML.getChildrenElementsByTagName(element, Constants.BODY)
				.get(0);
		Element elmBody = XML.getChildrenElements(elm).get(0);
		this.body = (Term) JavaClassesFactory.getTerm(elmBody);

		java.util.List<Element> its = XML.getChildrenElementsByTagName(element,
				Constants.COND);
		if (its.size() > 0)
			this.condition = (Term) JavaClassesFactory.getTerm(XML
					.getChildrenElements(its.get(0)).get(0));

		attributes = new HashMap<String, String>();
		its = XML.getChildrenElementsByTagName(element, Constants.ATTRIBUTES);
		// assumption: <attributes> appears only once
		if (its.size() > 0) {
			its = XML.getChildrenElements(its.get(0));
			for (Element e : its) {
				attributes.put(e.getAttribute(Constants.KEY_key_ATTR),
						e.getAttribute(Constants.VALUE_value_ATTR));
			}
		}
	}

	public String toString() {
		String content = "  context ";
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

	@Override
	public String toMaude() {
		return "mb context " + super.toMaude();
	}

	@Override
	public Element toXml(Document doc) {
		Element context = doc.createElement(Constants.CONTEXT);
		context.setTextContent("notimplementedyet");
		return context;
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}

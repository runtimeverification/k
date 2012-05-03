package ro.uaic.info.fmse.k;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map.Entry;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.utils.xml.XML;

public class Production extends ASTNode {
	java.util.List<ProductionItem> items;
	java.util.Map<String, String> attributes;

	public Production(Element element) {
		super(element);

		java.util.List<String> strings = new LinkedList<String>();
		strings.add(Constants.SORT);
		strings.add(Constants.TERMINAL);
		strings.add(Constants.USERLIST);
		java.util.List<Element> its = XML.getChildrenElementsByTagName(element, strings);

		items = new LinkedList<ProductionItem>();
		for (Element e : its)
			items.add((ProductionItem) JavaClassesFactory.getTerm(e));

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
		String content = "";
		for (ProductionItem i : items)
			content += i + " ";

		String attributes = "";
		for (Entry<String, String> entry : this.attributes.entrySet()) {
			String value = entry.getValue();
			if (!value.equals(""))
				value = "(" + value + ")";

			attributes += " " + entry.getKey() + value;
		}
		if (attributes.equals(""))
			return content;
		return content + "[" + attributes + "]";
	}
	@Override
	public String toMaude() {
		String content = "";
		for (ProductionItem pi : items)
		{
			if (pi instanceof Sort)
				content += pi + " ";
		}

		return content.trim();
	}
	
	public String getLabel()
	{
		return attributes.get("klabel");
	}
	
	public String getMetadata()
	{
		java.util.List<String> reject = new LinkedList<String>();
		reject.add("cons");
		reject.add("klabel");
		reject.add("latex");
		
		String attributes = "";
		for (Entry<String, String> entry : this.attributes.entrySet()) {
			if (!reject.contains(entry.getKey()))
			attributes += " " + entry.getKey() + "=(" + entry.getValue() + ")";
		}
		
		// append locations too
		attributes += " location=" + getMaudeLocation();
		
		return attributes.trim();
	}
}

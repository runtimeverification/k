package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map.Entry;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class Production extends ASTNode {
	protected java.util.List<ProductionItem> items;
	protected java.util.Map<String, String> attributes;

	public Production(Element element) {
		super(element);

		java.util.List<String> strings = new LinkedList<String>();
		strings.add(Constants.SORT);
		strings.add(Constants.TERMINAL);
		strings.add(Constants.USERLIST);
		java.util.List<Element> its = XML.getChildrenElementsByTagName(element, strings);

		items = new ArrayList<ProductionItem>();
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
		if (attributes.containsKey(Constants.CONS_cons_ATTR))
			DefinitionHelper.conses.put(attributes.get(Constants.CONS_cons_ATTR), this);
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
		for (ProductionItem pi : items) {
			if (pi.getType().equals(ProductionType.SORT))
				content += pi + " ";
		}

		return content.trim();
	}

	public String getLabel() {
		return attributes.get("prefixlabel");
	}

	public String getKLabel() {
		if (attributes.containsKey("klabel"))
			return attributes.get("klabel");
		return attributes.get("kgeneratedlabel");
	}

	public String getMetadata() {
		java.util.List<String> reject = new LinkedList<String>();
		reject.add("cons");
		reject.add("kgeneratedlabel");
		reject.add("latex");
		reject.add("prefixlabel");

		String attributes = "";
		for (Entry<String, String> entry : this.attributes.entrySet()) {
			if (!reject.contains(entry.getKey()))
				attributes += " " + entry.getKey() + "=(" + entry.getValue() + ")";
		}

		// append locations too
		attributes += " location=" + getMaudeLocation();

		return attributes.trim();
	}

	@Override
	public Element toXml(Document doc) {
		Element production = doc.createElement(Constants.PRODUCTION);

		for (ProductionItem pi : items)
			if (pi.toXml(doc) != null)
				production.appendChild(pi.toXml(doc));

		Element attributes = doc.createElement(Constants.ATTRIBUTES);
		production.appendChild(attributes);

		return production;
	}

	public java.util.List<ProductionItem> getItems() {
		return items;
	}

	public void setItems(java.util.List<ProductionItem> items) {
		this.items = items;
	}

	public java.util.Map<String, String> getAttributes() {
		return attributes;
	}

	public void setAttributes(java.util.Map<String, String> attributes) {
		this.attributes = attributes;
	}

	@Override
	public void all(Visitor visitor) {
		for (int i = 0; i < this.items.size(); i++) {
			ProductionItem elem = (ProductionItem) visitor.visit(this.items.get(i));
			this.items.set(i, elem);
		}
	}
}

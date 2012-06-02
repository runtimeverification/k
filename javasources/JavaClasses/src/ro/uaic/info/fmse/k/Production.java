package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.LinkedList;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Production extends ASTNode {
	protected java.util.List<ProductionItem> items;
	protected Attributes attributes;

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

		its = XML.getChildrenElementsByTagName(element, Constants.ATTRIBUTES);
		// assumption: <attributes> appears only once
		if (its.size() > 0) {
			attributes = (Attributes) JavaClassesFactory.getTerm(its.get(0));
		} else
			attributes = new Attributes("generated", "generated");
		if (attributes.containsKey(Constants.CONS_cons_ATTR))
			DefinitionHelper.conses.put(attributes.get(Constants.CONS_cons_ATTR), this);
	}

	public Production(Production node) {
		super(node);
		this.attributes = node.attributes;
		this.items = node.items;
	}

	public String toString() {
		String content = "";
		for (ProductionItem i : items)
			content += i + " ";

		return content + attributes.toString();
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

	public Attributes getAttributes() {
		return attributes;
	}

	public void setAttributes(Attributes attributes) {
		this.attributes = attributes;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		for (int i = 0; i < this.items.size(); i++) {
			ProductionItem elem = (ProductionItem) visitor.modify(this.items.get(i));
			this.items.set(i, elem);
		}
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
}

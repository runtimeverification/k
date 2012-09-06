package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.LinkedList;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Production extends ASTNode {
	protected java.util.List<ProductionItem> items;
	protected Attributes attributes;
	protected String sort;

	public boolean isListDecl() {
		return items.size() == 1 && items.get(0).getType() == ProductionType.USERLIST;
	}

	public boolean isSubsort() {
		return items.size() == 1 && items.get(0).getType() == ProductionType.SORT;
	}

	public boolean isConstant() {
		return items.size() == 1 && items.get(0).getType() == ProductionType.TERMINAL && (sort.startsWith("#") || sort.equals("KLabel"));
	}

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
			attributes = new Attributes();
	}

	public Production(Production node) {
		super(node);
		this.attributes = node.attributes;
		this.items = node.items;
	}

	public Production(Sort sort, java.util.List<ProductionItem> items) {
		super();
		this.items = items;
		this.sort = sort.getName();
		this.attributes = new Attributes();
	}

	public String toString() {
		String content = "";
		for (ProductionItem i : items)
			content += i + " ";

		return content;// + attributes.toString();
	}

	public boolean equals(Production other) {
		ArrayList<ProductionItem> p1List = (ArrayList<ProductionItem>) this.getItems();
		ArrayList<ProductionItem> p2List = (ArrayList<ProductionItem>) other.getItems();

		if (p1List.size() != p2List.size())
			return false;

		for (int i = 0; i < p1List.size(); i++) {
			ProductionItem p1Term = p1List.get(i);
			ProductionItem p2Term = p2List.get(i);

			if ((p1Term instanceof Terminal) && (p2Term instanceof Terminal))
				if (!((Terminal) p1Term).getTerminal().equals(((Terminal) p2Term).getTerminal()))
					return false;

				else if ((p1Term instanceof Sort) && (p2Term instanceof Sort))
					if (!((Sort) p1Term).getName().equals(((Sort) p2Term).getName()))
						return false;
					else {
						if (!(p1Term instanceof Sort) && !(p1Term instanceof Terminal))
							System.out.println("Not sort or terminal: " + p1Term);
						if (!(p2Term instanceof Sort) && !(p2Term instanceof Terminal))
							System.out.println("Not sort or terminal: " + p2Term);
						return false;
					}

		}
		return true;
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

	public String getCons() {
		return attributes.get("cons");
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

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (obj == this)
			return true;
		if (!(obj instanceof Production))
			return false;
		Production prd = (Production) obj;

		if (this.sort != null && prd.getSort() != null)
			if (!this.sort.equals(prd.getSort()))
				return false;
		if (this.sort == null && prd.getSort() != null)
			return false;

		if (prd.getItems().size() != this.items.size())
			return false;

		for (int i = 0; i < this.items.size(); i++) {
			if (!prd.getItems().get(i).equals(items.get(i)))
				return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		int hash = 0;
		if (sort != null)
			hash += sort.hashCode();

		for (ProductionItem pi : this.items)
			hash += pi.hashCode();
		return hash;
	}
	
	@Override
	public Production shallowCopy() {
		return new Production(this);
	}
}

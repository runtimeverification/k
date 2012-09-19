package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.loader.Constants;
import org.kframework.visitors.Modifier;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Document;
import org.w3c.dom.Element;


public class Sort extends ProductionItem {

	private String name;

	public Sort(Element element) {
		super(element);
		name = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public Sort(String name)
	{
		super();
		this.name = name;
	}
	
	public Sort(Sort sort) {
		super(sort);
		this.name = sort.name;
	}

	public static boolean isBasesort(String sort) {
		return sort.equals("VARID") || sort.equals("Map") || sort.equals("K") || sort.equals("List") || sort.equals("Bag") || sort.equals("Set") || sort.equals("MapItem") || sort.equals("ListItem") || sort.equals("BagItem") || sort.equals("SetItem")
				|| sort.equals("List{K}") || sort.equals("KLabel") || sort.equals("CellLabel");
	}
	
	public boolean isBaseSort() {
		return Sort.isBasesort(name);
	}

	public void setName(String sort) {
		this.name = sort;
	}

	public String getName() {
		return name;
	}

	public ProductionType getType() {
		return ProductionType.SORT;
	}

	@Override
	public String toString() {
		return name;
	}

	@Override
	public String toMaude() {
		return name;
	}

	@Override
	public Element toXml(Document doc) {
		// TODO Auto-generated method stub
		Element sort = doc.createElement(Constants.SORT);
		sort.setTextContent(this.name);

		return sort;
	}

	public void accept(Modifier visitor) {
		visitor.modify(this);
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (obj == this)
			return true;
		if (!(obj instanceof Sort))
			return false;

		Sort srt = (Sort) obj;

		if (!name.equals(srt.getName()))
			return false;
		return true;
	}

	@Override
	public int hashCode() {
		return this.name.hashCode();
	}

	@Override
	public Sort shallowCopy() {
		return new Sort(this);
	}
}

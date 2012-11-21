package org.kframework.kil;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

public class Sort extends ProductionItem {

	private String name;
	private static Set<String> baseSorts = new HashSet<String>();
	static {
		baseSorts.add("K");
		baseSorts.add("List{K}");
		baseSorts.add("Map");
		baseSorts.add("MapItem");
		baseSorts.add("List");
		baseSorts.add("ListItem");
		baseSorts.add("Set");
		baseSorts.add("SetItem");
		baseSorts.add("Bag");
		baseSorts.add("BagItem");
		baseSorts.add("KLabel");
		baseSorts.add("CellLabel");
	}

	public Sort(Element element) {
		super(element);
		name = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public Sort(String name) {
		super();
		this.name = name;
	}

	public Sort(Sort sort) {
		super(sort);
		this.name = sort.name;
	}

	public static boolean isBasesort(String sort) {
		return baseSorts.contains(sort);
	}

	public static Set<String> getBaseSorts() {
		return baseSorts;
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

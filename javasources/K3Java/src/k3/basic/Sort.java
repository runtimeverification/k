package k3.basic;

import k.utils.Tag;

import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

public class Sort extends Term implements Item {
	private String sort;
	
	public Sort clone() {
		Sort s = new Sort(sort);
		s.copy(this);
		return s;
	}

	public Sort(String sort) {
		this.sort = sort;
		location = "(0,0,0,0)";
		filename = "generated";
	}

	public Sort(Node node, String fileName) {
		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.value);
		sort = item.getNodeValue();
		item = attr.getNamedItem(Tag.location);
		location = item.getNodeValue();
		filename = fileName;
		xmlTerm = node;
	}

	public boolean isBaseSort() {
		return sort.equals("VARID") || sort.equals("Map") || sort.equals("K") || sort.equals("List") || sort.equals("Bag") || sort.equals("Set") || sort.equals("MapItem")
				|| sort.equals("ListItem") || sort.equals("BagItem") || sort.equals("SetItem") || sort.equals("List{K}") || sort.equals("KLabel");
	}

	public String getSortName() {
		return sort;
	}

	@Override
	public String toString() {
		return sort;
	}

	@Override
	public ItemType getType() {
		return ItemType.SORT;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (o.getClass() == Sort.class) {
			Sort s1 = (Sort) o;
			return s1.getSortName().equals(sort);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return sort.hashCode();
	}
}

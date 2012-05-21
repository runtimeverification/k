package k3.basic;

import java.util.*;

import k.utils.Tag;
import k3.basic.Item.ItemType;

import org.w3c.dom.*;

public class Production extends Term implements Cloneable {
	private List<Item> items;
	private Map<String, String> attributes;
	private Sort prodSort;

	public Production clone() {
		Production p = new Production();
		p.copy(this);

		p.prodSort = prodSort;
		for (Map.Entry<String, String> es : attributes.entrySet())
			p.attributes.put(es.getKey(), es.getValue());

		for (Item i : items)
			p.items.add(i.clone());

		return p;
	}

	public Production() {
		items = new ArrayList<Item>();
		attributes = new HashMap<String, String>();
	}

	public Production(Node node, Sort pSort) {
		super(node);
		items = new ArrayList<Item>();
		attributes = new HashMap<String, String>();
		setProdSort(pSort);

		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.location);
		setLocation(item.getNodeValue());

		NodeList children = node.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			if (children.item(i).getNodeName().equals(Tag.sort)) {
				items.add(new Sort(children.item(i)));
			} else if (children.item(i).getNodeName().equals(Tag.terminal)) {
				items.add(new Terminal(children.item(i)));
			} else if (children.item(i).getNodeName().equals(Tag.userlist)) {
				items.add(new UserList(children.item(i)));
			} else if (children.item(i).getNodeName().equals(Tag.attributes)) {
				NodeList ch = ((Element) children.item(i)).getElementsByTagName(Tag.tag);
				for (int j = 0; j < ch.getLength(); j++) {
					Node child = ch.item(j);

					NamedNodeMap attrs = child.getAttributes();
					item = attrs.getNamedItem(Tag.key);
					String tagname = item.getNodeValue();

					String tagvalue = "";
					if (attrs.getNamedItem(Tag.value) != null) {
						item = attrs.getNamedItem(Tag.value);
						tagvalue = item.getNodeValue();
					}
					if (tagname.equals("cons")) // unquote the cons attribute
						tagvalue = tagvalue.substring(0, tagvalue.length() - 1).substring(1);
					attributes.put(tagname, tagvalue);
				}
			}
		}
	}

	public void collapseSorts() {
		// collapse all of the user defined sorts, to the K sort
		for (int i = 0; i < items.size(); i++) {
			if (items.get(i).getType() == ItemType.SORT) {
				Sort s = (Sort) items.get(i);
				if (!s.isBaseSort()) {
					items.remove(i);
					items.add(i, new Sort("K"));
				}
			}
		}
		if (!prodSort.isBaseSort()) {
			prodSort = new Sort("K");
		}
	}

	public List<Item> getItems() {
		return items;
	}

	@Override
	public String toString() {
		String out = "";
		for (Item item : items) {
			out += item.toString() + " ";
		}

		return out;
	}

	public List<Sort> getSorts() {
		List<Sort> sorts = new ArrayList<Sort>();
		for (Item i : items)
			if (i.getType() == ItemType.SORT)
				sorts.add((Sort) i);
		return sorts;
	}

	public boolean isSubsort() {
		if (items.size() == 1 && items.get(0).getType() == ItemType.SORT) {
			return true;
		}

		return false;
	}

	public boolean isListDecl() {
		if (items.size() == 1 && items.get(0).getType() == ItemType.USERLIST) {
			return true;
		}

		return false;
	}

	public Sort getProdSort() {
		return prodSort;
	}

	public void setProdSort(Sort prodSort) {
		this.prodSort = prodSort;
	}

	public Map<String, String> getAttributes() {
		return attributes;
	}

	public void setAttributes(Map<String, String> attributes) {
		this.attributes = attributes;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (o.getClass() == Production.class) {
			Production p1 = (Production) o;
			if (!p1.prodSort.equals(prodSort))
				return false;
			if (p1.items.size() != items.size())
				return false;

			for (int i = 0; i < items.size(); i++) {
				if (!p1.items.get(i).equals(items.get(i)))
					return false;
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		int hash = prodSort.hashCode();
		for (Item i : items) {
			hash += i.hashCode();
		}
		return hash;
	}
}

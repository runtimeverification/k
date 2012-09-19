package org.kframework.parser.generator.basic;


import org.kframework.utils.Tag;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

public class UserList extends Term implements Item {
	private Sort sort;
	private String terminal;

	public UserList clone() {
		UserList ul = new UserList(sort, terminal);
		ul.copy(this);
		return ul;
	}

	public UserList(Sort sort, String terminal) {
		this.sort = sort;
		location = "(0,0,0,0)";
		filename = "generated";
		this.terminal = terminal;
	}

	public UserList(Node node) {
		super(node);
		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.value);
		sort = new Sort(item.getNodeValue());

		item = attr.getNamedItem(Tag.separator);
		terminal = item.getNodeValue();
	}

	@Override
	public String toString() {
		return sort.toString();
	}

	@Override
	public ItemType getType() {
		return ItemType.USERLIST;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (o.getClass() == UserList.class) {
			UserList s1 = (UserList) o;
			return s1.getSort().equals(sort) && s1.getTerminal().equals(terminal);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return sort.hashCode() + terminal.hashCode();
	}

	public void setTerminal(String terminal) {
		this.terminal = terminal;
	}

	public String getTerminal() {
		return terminal;
	}

	public Sort getSort() {
		return sort;
	}

	public void setSort(Sort sort) {
		this.sort = sort;
	}
}

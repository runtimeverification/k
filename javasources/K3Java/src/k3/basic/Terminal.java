package k3.basic;

import k.utils.Tag;

import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

public class Terminal extends Term implements Item {
	private String terminal;

	public Terminal clone() {
		Terminal tl = new Terminal(terminal);
		tl.copy(this);
		return tl;
	}

	public Terminal(String terminal) {
		this.terminal = terminal;
		filename = "generated";
		location = "(0,0,0,0)";
	}

	public Terminal(Node node) {
		super(node);
		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.value);
		terminal = item.getNodeValue();
	}

	public String getTerminal() {
		return terminal;
	}

	@Override
	public String toString() {
		return terminal;
	}

	@Override
	public ItemType getType() {
		return ItemType.TERMINAL;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (o.getClass() == Terminal.class) {
			Terminal s1 = (Terminal) o;
			return s1.getTerminal().equals(terminal);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return terminal.hashCode();
	}
}

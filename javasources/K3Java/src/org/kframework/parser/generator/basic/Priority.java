package org.kframework.parser.generator.basic;

import java.util.*;


import org.kframework.utils.Tag;
import org.w3c.dom.*;

public class Priority extends Term {
	private List<Production> productions = new ArrayList<Production>();
	private String blockAssoc = null;

	public Priority clone() {
		Priority p = new Priority();
		p.copy(this);
		p.blockAssoc = blockAssoc;
		for (Production p2 : productions)
			p.productions.add(p2.clone());
		return p;
	}

	public String getBlockAssoc() {
		return blockAssoc;
	}

	public void setBlockAssoc(String blockAssoc) {
		this.blockAssoc = blockAssoc;
	}

	public Priority() {
	}

	public Priority(Node node, Sort pSort) {
		super(node);

		setProductions(new ArrayList<Production>());

		NamedNodeMap attr = node.getAttributes();

		Node item = attr.getNamedItem(Tag.assoc);
		if (item != null)
			blockAssoc = item.getNodeValue();

		NodeList children = node.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			if (children.item(i).getNodeName().equals(Tag.production)) {
				productions.add(new Production(children.item(i), pSort));
			}
		}
	}

	public List<Production> getProductions() {
		return productions;
	}

	public void setProductions(List<Production> productions) {
		this.productions = productions;
	}
}

package k3.basic;

import java.util.*;

import k.utils.Tag;

import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class Syntax extends Sentence {
	private Sort sort;
	private List<Priority> priorities;
	
	public Syntax clone() {
		super.clone();
		
		Syntax s = new Syntax();
		s.copy(this);
		s.sort = this.sort;
		for (Priority p : priorities)
			s.priorities.add(p.clone());
		
		return s;
	}

	public Syntax() {
		priorities = new ArrayList<Priority>();
	}

	public List<Priority> getPriorities() {
		return priorities;
	}

	public void setPriorities(List<Priority> priorities) {
		this.priorities = priorities;
	}

	public Syntax(Node node, String filename) {
		// set file name
		this.filename = filename;
		this.xmlTerm = node;
		// set everything
		priorities = new ArrayList<Priority>();

		Node item = node.getAttributes().getNamedItem(Tag.location);
		location = item.getNodeValue();

		NodeList children = node.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			if (children.item(i).getNodeName().equals(Tag.sort)) {
				NamedNodeMap attr = children.item(i).getAttributes();
				item = attr.getNamedItem(Tag.value);
				sort = new Sort(item.getNodeValue());

				item = attr.getNamedItem(Tag.location);
				this.location = item.getNodeValue();
			} else if (children.item(i).getNodeName().equals(Tag.priority)) {
				priorities.add(new Priority(children.item(i), filename, sort));
			}
		}
	}

	@Override
	public SentenceType getType() {
		return SentenceType.SYNTAX;
	}

	public Sort getSort() {
		return sort;
	}

	public void setSort(Sort sort) {
		this.sort = sort;
	}

	public List<Production> getProductions() {
		List<Production> prod = new ArrayList<Production>();
		for (Priority p : priorities) {
			prod.addAll(p.getProductions());
		}
		return prod;
	}
}

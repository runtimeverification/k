package k3.basic;

import java.util.ArrayList;
import java.util.List;

import k.utils.Tag;

import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class Syntax extends Sentence {
	private Sort sort;
	private List<Priority> priorities;

	public Syntax clone() {
		super.clone();

		Syntax s = new Syntax(this);
		return s;
	}

	public Syntax(Syntax s) {
		super(s);
		priorities = new ArrayList<Priority>();
		this.sort = s.sort;
		for (Priority p : s.priorities)
			this.priorities.add(p.clone());
	}

	public List<Priority> getPriorities() {
		return priorities;
	}

	public void setPriorities(List<Priority> priorities) {
		this.priorities = priorities;
	}

	public Syntax(Node node) {
		super(node);
		// set everything
		priorities = new ArrayList<Priority>();

		NodeList children = node.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			if (children.item(i).getNodeName().equals(Tag.sort)) {
				sort = new Sort(children.item(i));
			} else if (children.item(i).getNodeName().equals(Tag.priority)) {
				priorities.add(new Priority(children.item(i), sort));
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

package ro.uaic.info.fmse.ca;

import java.util.LinkedList;
import java.util.List;

import ro.uaic.info.fmse.utils.Generator;

public class Node {

	private int ID;
	private String label;
	private List<Node> children;
	private Node parent;
	private Object data;

	public Node(String label, List<Node> children, Node parent, Object data) {
		this(Generator.getNewId(), label, children, parent, data);
	}

	private Node(int iD, String label, List<Node> children, Node parent,
			Object data) {
		super();
		ID = iD;
		setLabel(label);
		setChildren(children);
		setParent(parent);
		setData(data);
	}

	public Integer getID() {
		return ID;
	}

	public String getLabel() {
		return label;
	}

	public void setLabel(String label) {
		this.label = label;
	}

	public List<Node> getChildren() {
		return children;
	}

	public Node getParent() {
		return parent;
	}

	public Object getData() {
		return data;
	}

	public void setChildren(List<Node> children) {
		this.children = children;
	}

	public void setParent(Node parent) {
		this.parent = parent;
	}

	public void setData(Object data) {
		this.data = data;
	}

	public void appendChildren(Node... child)
	{
		if (children == null)
			children = new LinkedList<Node>();
		
		for (Node c : child)
			children.add(c);
	}
	
	@Override
	protected Object clone() throws CloneNotSupportedException {

		List<Node> children = new LinkedList<Node>();
		for (Node child : this.children)
			children.add((Node) child.clone());

		return new Node(ID, label, children, (Node) parent.clone(), data);
	}

	public String display(String tabs) {
		String out = "";

		String children = "";

		for (Node child : this.children)
			children += child.display(tabs + "\t");

		out += tabs + "<" + label + " id=" + ID + ">\n" + children + tabs + "</" + label + ">\n";

		return out;
	}

	public List<Node> getDescendants() {
		List<Node> descendants = new LinkedList<Node>();

		// collect children and their descendants
		if (children.size() > 0)
			for (Node child : children) {
				descendants.add(child);
				descendants.addAll(child.getDescendants());
			}

		return descendants;
	}
	
	@Override
	public String toString() {
//		return "Node: " + label + " id: " + ID + " children:[" + children.toString() + "]  parent: " + parent;
		
		String children = "";
		for (Node child : this.children)
			children += child.label + " ";
		
		if (parent == null)
			return "Node: " + label + " id: " + ID + " parent: null children: " + children ;
		return "Node: " + label + " id: " + ID + " parent: " + parent.getLabel() + " children: " + children;
		}
}

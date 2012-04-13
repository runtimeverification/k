package ro.uaic.info.fmse.ca;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class Rule {

	List<Node> lhs, rhs, left, right;
	Map<Integer, Integer> left2right, right2left;

	public Rule(Element rule) {

		// init
		left = new LinkedList<Node>();
		right = new LinkedList<Node>();
		left2right = new HashMap<Integer, Integer>();
		right2left = new HashMap<Integer, Integer>();

		// this assumes that rule has only one <left> tag and one <right> tag
		Element left = (Element) rule.getElementsByTagName("left").item(0);
		Element right = (Element) rule.getElementsByTagName("right").item(0);

		// BUILD THE TREE-LIKE STRUCTURE AND THE LISTS OF NODES
		lhs = recurseInto(left, this.left);
		rhs = recurseInto(right, this.right);

		// compute parent relation
		if (lhs != null)
			for (Node lh : lhs)
				addParent(lh, null);

		if (rhs != null)
			for (Node rh : rhs)
				addParent(rh, null);

//		// create the left to right map
//		mapSide("left");
//		mapSide("right");

		// System.out.println("\n\n\n\nCreated: rule ");
		// for(Node lh : this.left)
		// System.out.println(lh.display(""));
		// System.out.println("=>");
		// for(Node rh : this.right)
		// System.out.println(rh.display(""));
		// System.out.println("\nFor: ");
		// System.out.println(XMLPrettyPrinter.prettyFormat(rule));
	}

//	private void mapSide(String side) {
//		if (side.equals("left")) {
//			for (Node left : this.left)
//				for (Node right : this.right)
//					if (left.getData().equals(right.getData()))
//						left2right.put(left.getID(), right.getID());
//		}
//		if (side.equals("left")) {
//			for (Node right : this.right)
//				for (Node left : this.left)
//					if (left.getData().equals(right.getData()))
//						right2left.put(right.getID(), left.getID());
//		}
//	}

	private Node createEmptyNodeFromElement(Element cell) {
		Node node = null;
		if (cell.getNodeName().equals("cell")) {
			String label = cell.getAttribute("label");
			node = new Node(label, new LinkedList<Node>(), null, cell);
		}

		return node;
	}

	private List<Node> recurseInto(Element cell, List<Node> collect) {

		List<Node> nodes = new LinkedList<Node>();

		// recurse - this is very specific to KIL
		NodeList children = cell.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			org.w3c.dom.Node nnode = children.item(i);
			if (nnode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				Element n = (Element) nnode;
				if (n.getNodeName().equals("cell")) {
					Node node = createEmptyNodeFromElement(n);
					node.setChildren(recurseInto(n, collect));
					nodes.add(node);
					collect.add(node);
				} else
					nodes.addAll(recurseInto(n, collect));
			}
		}
		return nodes;
	}

	private void addParent(Node root, Node parent) {
		root.setParent(parent);

		List<Node> children = root.getChildren();
		for (Node child : children)
			addParent(child, root);
	}

	@Override
	public String toString() {
		String out = "";

		if (lhs != null)
			for (Node root : this.lhs)
				out += root.display("");

		out += " => ";

		if (rhs != null)
			for (Node root : this.rhs)
				out += root.display("");

		out += "Left: " + left2right + "\nRight: " + right2left;

		return out;
	}

	public List<Node> getLhs() {
		return lhs;
	}

	public List<Node> getRhs() {
		return rhs;
	}

	public List<Node> getLeft() {
		return left;
	}

	public List<Node> getRight() {
		return right;
	}
}

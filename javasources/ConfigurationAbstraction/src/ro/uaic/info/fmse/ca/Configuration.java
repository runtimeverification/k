package ro.uaic.info.fmse.ca;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class Configuration {
	
	// tree-like configuration
	private List<Node> roots;
	
	// the complete list of nodes.
	private List<Node> nodes;
	
	// multiplicity map
	private Map<Integer, Integer> mmap;

	public Configuration(List<Node> roots, List<Node> nodes, Map<Integer, Integer> mmap)
	{
		this.roots = roots;
		this.nodes = nodes;
		this.mmap = mmap;
	}
	
	public Configuration(Element configuration) {
		mmap = new HashMap<Integer, Integer>();
		nodes = new LinkedList<Node>();
		initFromXML(configuration);
	}

	public Integer multiplicity(Node node) {
		return mmap.get(node.getID());
	}
	
	public Integer multiplicity(Integer entry) {
		if (entry == null)
			return -1;
		
		return mmap.get(entry) == null ? 1 : mmap.get(entry) ;
	}

	
	private void initFromXML(Element configuration) {

		// create nodes from XML
		roots = recurseInto(configuration);

		// add parent relation
		if (roots != null)
			for(Node root : this.roots)
				addParent(root, null);

		// collect nodes in list - don't do it for now
		// appendNodes(root);
	}

	private void addParent(Node root, Node parent) {
		root.setParent(parent);

		List<Node> children = root.getChildren();
		for (Node child : children)
			addParent(child, root);
	}

	private Node createEmptyNodeFromElement(Element cell) {
		Node node = null;
		if (cell.getNodeName().equals("cell")) {
			String label = cell.getAttribute("label");
			node = new Node(label, new LinkedList<Node>(), null, cell);
			String multiplicity = cell.getAttribute("multiplicity");
			if (multiplicity != null)
				if (multiplicity.equals("*") || multiplicity.equals("+"))
					mmap.put(node.getID(), Integer.MAX_VALUE);
				else if (multiplicity.equals("?"))
					mmap.put(node.getID(), 1);
				else
					mmap.put(node.getID(), 1);
		}

		return node;
	}

	private List<Node> recurseInto(Element cell) {

		List<Node> nodes = new LinkedList<Node>();

		// recurse - this is very specific to KIL
		NodeList children = cell.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			org.w3c.dom.Node nnode = children.item(i);
			if (nnode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				Element n = (Element) nnode;
				if (n.getNodeName().equals("cell")) {
					Node node = createEmptyNodeFromElement(n);
					node.setChildren(recurseInto(n));
					nodes.add(node);
					this.nodes.add(node);
				} else
					nodes.addAll(recurseInto(n));
			}
		}

		return nodes;
	}

	@Override
	public String toString() {
		String out = "";

		if (roots != null)
			for (Node root : this.roots)
				out += root.display("");

		return out;
	}

	public List<Integer> searchIds(Node l) {
		
		List<Integer> result = new LinkedList<Integer>();
		for (Node cfg : nodes)
		{
			if (cfg.getLabel().equals(l.getLabel()))
				result.add(cfg.getID());
		}
		return result;
	}

}

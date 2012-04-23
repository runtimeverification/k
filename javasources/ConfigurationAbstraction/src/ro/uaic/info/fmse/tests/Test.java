package ro.uaic.info.fmse.tests;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;

public class Test {

	public Configuration getConfig() {

		Node T = new Node("T", new LinkedList<Node>(), null, null);
		Node a = new Node("a", new LinkedList<Node>(), null, null);
		Node b = new Node("b", new LinkedList<Node>(), null, null);
		Node d = new Node("d", new LinkedList<Node>(), null, null);
		Node m = new Node("m", new LinkedList<Node>(), null, null);
		Node n = new Node("n", new LinkedList<Node>(), null, null);
		Node f = new Node("f", new LinkedList<Node>(), null, null);
		Node h = new Node("h", new LinkedList<Node>(), null, null);
		Node h2 = new Node("h", new LinkedList<Node>(), null, null);
		Node pn = new Node("n", new LinkedList<Node>(), null, null);
		Node g = new Node("g", new LinkedList<Node>(), null, null);
		Node o = new Node("o", new LinkedList<Node>(), null, null);
		Node l = new Node("l", new LinkedList<Node>(), null, null);
		Node c = new Node("c", new LinkedList<Node>(), null, null);
		Node e = new Node("e", new LinkedList<Node>(), null, null);
		Node i = new Node("i", new LinkedList<Node>(), null, null);
		Node j = new Node("j", new LinkedList<Node>(), null, null);
		Node k = new Node("k", new LinkedList<Node>(), null, null);
		Node r = new Node("r", new LinkedList<Node>(), null, null);
		Node s = new Node("s", new LinkedList<Node>(), null, null);

		n.appendChildren(o);
		m.appendChildren(n);
		d.appendChildren(l, m);
		a.appendChildren(c, d, e);
		h.appendChildren(i, j, k);
		f.appendChildren(g, h);
		pn.appendChildren(r, s);
		h2.appendChildren(pn);
		b.appendChildren(f, h2);
		T.appendChildren(a, b);

		List<Node> roots = new LinkedList<Node>();
		roots.add(T);
		
		List<Node> nodes = createListOfNodes(T, a, b, d, m, n, f, h, h2, pn, g,
				o, l, c, e, i, j, k, r, s);
		
		Map<Integer, Integer> mmap = new HashMap<Integer, Integer>();
		mmap.put(n.getID(), Integer.MAX_VALUE);
		
		return new Configuration(roots, nodes, mmap);
		
	}
	
	public Rule getRule1()
	{
		Node d = new Node("d", new LinkedList<Node>(), null, null);
		Node h = new Node("h", new LinkedList<Node>(), null, null);
		Node n1 = new Node("n", new LinkedList<Node>(), null, null);
		Node n2 = new Node("n", new LinkedList<Node>(), null, null);
		Node s = new Node("s", new LinkedList<Node>(), null, null);
		
		d.appendChildren(n1, n2);
		h.appendChildren(s);
		
		List<Node> roots = new LinkedList<Node>();
		roots.add(d);
		roots.add(h);
		
		List<Node> nodes = createListOfNodes(d,h,n1, n2, s);
		
		return new Rule(roots, null, nodes, null);
	}

	public Rule getRule2()
	{
		Node d = new Node("d", new LinkedList<Node>(), null, null);
		Node h = new Node("h", new LinkedList<Node>(), null, null);
		Node n1 = new Node("n", new LinkedList<Node>(), null, null);
		Node n2 = new Node("u", new LinkedList<Node>(), null, null);
		Node s = new Node("s", new LinkedList<Node>(), null, null);
		
		d.appendChildren(n1, n2);
		h.appendChildren(s);
		
		List<Node> roots = new LinkedList<Node>();
		roots.add(d);
		roots.add(h);
		
		List<Node> nodes = createListOfNodes(d,h,n1, n2, s);
		
		return new Rule(roots, null, nodes, null);
	}

	
	List<Node> createListOfNodes(Node... nodes) {
		List<Node> list = new LinkedList<Node>();
		for (Node n : nodes)
			list.add(n);

		return list;
	}
}

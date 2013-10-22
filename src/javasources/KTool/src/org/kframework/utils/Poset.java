package org.kframework.utils;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

public class Poset implements Serializable {

	private java.util.Set<Tuple> relations = new HashSet<Tuple>();
	private java.util.Set<String> elements = new HashSet<String>();

	public void addRelation(String big, String small) {
		relations.add(new Tuple(big, small));
		elements.add(big);
		elements.add(small);
	}

	public boolean isInRelation(String big, String small) {
		return relations.contains(new Tuple(big, small));
	}

	public void transitiveClosure() {
		boolean finished = false;
		while (!finished) {
			finished = true;
			Set<Tuple> ssTemp = new HashSet<Tuple>();
			for (Tuple s1 : relations) {
				for (Tuple s2 : relations) {
					if (s1.big.equals(s2.small)) {
						Tuple sTemp = new Tuple(s2.big, s1.small);
						if (!relations.contains(sTemp)) {
							ssTemp.add(sTemp);
							finished = false;
						}
					}
				}
			}
			relations.addAll(ssTemp);
		}
	}

	public String getMaxim(String start) {
		boolean maxim = true;
		do {
			maxim = true;
			for (Tuple sbs : relations) {
				if (sbs.small.equals(start)) {
					start = sbs.big;
					maxim = false;
				}
			}
		} while (!maxim);
		return start;
	}

	/**
	 * finds the least upper bound of a subset of the elements of
	 * 
	 * returns null if none exists
	 * 
	 * assumes that all elements in subset are actually elements of the Poset
	 * 
	 * also assumes that the Poset is actually a Poset (transitively closed)
	 * 
	 */
	public String getLUB(Set<String> subset) {
		if (subset == null || subset.size() == 0)
			return null;
		if (subset.size() == 1)
			return subset.iterator().next();
		List<String> candidates = new ArrayList<String>();
		for (String elem : elements) {
			boolean isGTESubset = true;
			for (String subsetElem : subset) {
				if (!(isInRelation(elem, subsetElem) || elem.equals(subsetElem))) {
					isGTESubset = false;
					break;
				}
			}
			if (isGTESubset) {
				candidates.add(elem);
			}
		}
		if (candidates.size() == 0)
			return null;
		String lub = candidates.get(0);
		for (int i = 1; i < candidates.size(); ++i) {
			if (isInRelation(lub, candidates.get(i))) {
				lub = candidates.get(i);
			}
		}
		return lub;
	}

	/**
	 * finds the greatest lower bound of a subset of the elements of
	 * 
	 * returns null if none exists
	 * 
	 * assumes that all elements in subset are actually elements of the Poset
	 * 
	 * also assumes that the Poset is actually a Poset (transitively closed)
	 * 
	 */
	public String getGLB(Set<String> subset) {
		if (subset == null || subset.size() == 0)
			return null;
		if (subset.size() == 1)
			return subset.iterator().next();
		List<String> candidates = new ArrayList<String>();
		for (String elem : elements) {
			boolean isLTESubset = true;
			for (String subsetElem : subset) {
				if (!(isInRelation(subsetElem, elem) || elem.equals(subsetElem))) {
					isLTESubset = false;
					break;
				}
			}
			if (isLTESubset) {
				candidates.add(elem);
			}
		}
		if (candidates.size() == 0)
			return null;
		String glb = candidates.get(0);
		for (int i = 1; i < candidates.size(); ++i) {
			if (isInRelation(candidates.get(i), glb)) {
				glb = candidates.get(i);
			}
		}
		return glb;
	}

	private class Tuple implements Serializable {
		private String big, small;

		public Tuple(String big, String small) {
			this.big = big;
			this.small = small;
		}

		@Override
		public boolean equals(Object o) {
			if (o == null)
				return false;
			if (o.getClass() == Tuple.class) {
				Tuple s1 = (Tuple) o;
				return s1.big.equals(big) && s1.small.equals(small);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return big.hashCode() + small.hashCode();
		}

		@Override
		public String toString() {
			return small + " < " + big;
		}
	}

	/**
	 * Checks to see if the current set of relations has a circuit.
	 * 
	 * @return null if there aren't any circuits, or a list of relations that create a circuit.
	 */
	public List<String> checkForCycles() {
		// make next node list
		Set<String> nodes = new HashSet<String>();
		Set<String> visited = new HashSet<String>();

		for (Tuple t : relations) {
			nodes.add(t.big);
			nodes.add(t.small);
		}

		// DFS to search for a cycle
		for (String node : nodes) {
			if (!visited.contains(node)) {
				Stack<String> nodesStack = new Stack<String>();
				Stack<Iterator<String>> iteratorStack = new Stack<Iterator<String>>();
				nodesStack.push(node);
				visited.add(node);
				iteratorStack.push(nodes.iterator());

				while (nodesStack.size() > 0) {
					Iterator<String> currentIterator = iteratorStack.peek();
					String currentNode = nodesStack.peek();
					while (currentIterator.hasNext()) {
						String nextNode = currentIterator.next();
						if (relations.contains(new Tuple(nextNode, currentNode))) {
							if (nodesStack.contains(nextNode)) {
								List<String> circuit = new ArrayList<String>();
								for (int i = nodesStack.indexOf(nextNode); i < nodesStack.size(); i++) {
									circuit.add(nodesStack.elementAt(i));
								}
								return circuit;
							}
							if (!visited.contains(nextNode)) {
								nodesStack.push(nextNode);
								iteratorStack.push(nodes.iterator());
								visited.add(nextNode);
								break;
							}
						}
					}
					// does not have next... pop
					if (!currentIterator.hasNext()) {
						nodesStack.pop();
						iteratorStack.pop();
					}
				}
			}
		}
		return null;
	}

	// a small test to verify if LUB works
	// should print Exps
	public static void main(String[] args) {
		System.out.println("msg");
		Poset p = new Poset();
		p.addRelation("K", "Exps");
		p.addRelation("Exps", "Vals");
		p.addRelation("Exps", "Ids");
		p.transitiveClosure();
		Set<String> input = new HashSet<String>();
		input.add("K");
		input.add("Exps");
		input.add("Vals");
		input.add("Ids");
		System.out.println(p.getLUB(input));
	}
}

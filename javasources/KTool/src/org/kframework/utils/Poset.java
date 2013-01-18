package org.kframework.utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

public class Poset {

	private java.util.Set<Tuple> relations = new HashSet<Tuple>();

	public void addRelation(String big, String small) {
		relations.add(new Tuple(big, small));
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

	private class Tuple {
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
	 * @return null if there aren't any circuits, or a list of relations that create a circuit.
	 */
	public List<String> checkForCycles() {
		// make next node list
		Set<String> nodes = new HashSet<String>();
		Set<String> vizited = new HashSet<String>();

		for (Tuple t : relations) {
			nodes.add(t.big);
			nodes.add(t.small);
		}

		// DFS to search for a cycle
		for (String node : nodes) {
			if (!vizited.contains(node)) {
				Stack<String> nodesStack = new Stack<String>();
				Stack<Iterator<String>> iteratorStack = new Stack<Iterator<String>>();
				nodesStack.push(node);
				vizited.add(node);
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
							if (!vizited.contains(nextNode)) {
								nodesStack.push(nextNode);
								iteratorStack.push(nodes.iterator());
								vizited.add(nextNode);
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
}

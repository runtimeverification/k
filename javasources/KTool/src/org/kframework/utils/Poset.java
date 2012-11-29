package org.kframework.utils;

import java.util.HashSet;
import java.util.Set;

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
	}
}

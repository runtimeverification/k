package org.kframework.kil.loader;

import java.util.*;

public class Subsort {
	private String bigSort, smallSort;

	public Subsort(String bigSort, String smallSort) {
		this.bigSort = bigSort;
		this.smallSort = smallSort;
	}

	public String getBigSort() {
		return bigSort;
	}

	public String getSmallSort() {
		return smallSort;
	}

	@Override
	public String toString() {
		return smallSort + "<" + bigSort;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (o.getClass() == Subsort.class) {
			Subsort s1 = (Subsort) o;
			return s1.bigSort.equals(bigSort) && s1.smallSort.equals(smallSort);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return bigSort.hashCode() + smallSort.hashCode();
	}

	public static Set<Subsort> getDefaultSubsorts() {
		Set<Subsort> sbs = new HashSet<Subsort>();
		sbs.add(new Subsort("List{K}", "K"));
		sbs.add(new Subsort("Map", "MapItem"));
		sbs.add(new Subsort("Set", "SetItem"));
		sbs.add(new Subsort("List", "ListItem"));
		sbs.add(new Subsort("Bag", "BagItem"));

		return sbs;
	}
}

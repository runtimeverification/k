package org.kframework.parser.generator.basic;

import java.util.*;

public class Subsort extends Term {
	private Sort bigSort, smallSort;

	public Subsort(Sort bigSort, Sort smallSort, String filename, String location) {
		this.bigSort = bigSort;
		this.smallSort = smallSort;
		this.setFilename(filename);
		this.setLocation(location);
	}

	public Subsort(Sort bigSort, Sort smallSort) {
		this.bigSort = bigSort;
		this.smallSort = smallSort;
		filename = "generated";
		location = "(0,0,0,0)";
	}

	public Sort getBigSort() {
		return bigSort;
	}

	public Sort getSmallSort() {
		return smallSort;
	}

	@Override
	public String toString() {
		return bigSort + "<" + smallSort;
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
		sbs.add(new Subsort(new Sort("List{K}"), new Sort("K")));
		sbs.add(new Subsort(new Sort("Map"), new Sort("MapItem")));
		sbs.add(new Subsort(new Sort("Set"), new Sort("SetItem")));
		sbs.add(new Subsort(new Sort("List"), new Sort("ListItem")));
		sbs.add(new Subsort(new Sort("Bag"), new Sort("BagItem")));

		return sbs;
	}
}

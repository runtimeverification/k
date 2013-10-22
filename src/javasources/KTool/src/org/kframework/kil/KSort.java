package org.kframework.kil;

public enum KSort {
	K, Bag, Set, Map, List, BagItem, SetItem, MapItem, ListItem, KItem, KList, CellLabel, KLabel, ;

	public static KSort getKSort(String sort) {
		try {
			return valueOf(sort);
		} catch (Exception e) {
			return K;
		}
	}

	public KSort mainSort() {
		switch (this) {
		case Bag:
		case BagItem:
			return Bag;
		case Map:
		case MapItem:
			return Map;
		case Set:
		case SetItem:
			return Set;
		case List:
		case ListItem:
			return List;
		case KItem:
			return K;
		default:
			return this;
		}
	}

	public boolean isDefaultable() {
		return (this == Map || this == Bag || this == List || this == Set || this == K);
	}
}

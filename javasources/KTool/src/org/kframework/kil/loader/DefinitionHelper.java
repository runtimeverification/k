package org.kframework.kil.loader;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.kil.Cell;
import org.kframework.kil.Constant;
import org.kframework.kil.Production;
import org.kframework.kil.UserList;

public class DefinitionHelper {
	public static Set<String> generatedTags = new HashSet<String>();
	static {
		generatedTags.add("cons");
		generatedTags.add("kgeneratedlabel");
		generatedTags.add("prefixlabel");
	};

	public static Set<String> parsingTags = new HashSet<String>();

	static {
		parsingTags.add("left");
		parsingTags.add("right");
		parsingTags.add("non-assoc");
	}

	public static Set<String> specialTerminals = new HashSet<String>();

	static {
		specialTerminals.add("(");
		specialTerminals.add(")");
		specialTerminals.add(",");
		specialTerminals.add("[");
		specialTerminals.add("]");
		specialTerminals.add("{");
		specialTerminals.add("}");
	};

	public static java.util.Map<String, Production> conses = new HashMap<String, Production>();
	public static java.util.Map<String, Cell> cells = new HashMap<String, Cell>();
	public static java.util.Map<String, String> cellSorts = new HashMap<String, String>();
	public static java.util.Map<String, Production> listConses = new HashMap<String, Production>();
	private static java.util.Set<Subsort> subsorts = Subsort.getDefaultSubsorts();
	private static java.util.Set<Subsort> fileRequirements = new HashSet<Subsort>();

	public static void addCellDecl(Cell c) {
		cells.put(c.getLabel(), c);

		String sort = c.getContents().getSort();
		boolean maxim = true;
		do {
			maxim = true;
			for (Subsort sbs : subsorts) {
				if (sbs.getSmallSort().equals(sort)) {
					sort = sbs.getBigSort();
					maxim = false;
				}
			}
		} while (!maxim);

		if (sort.equals("List{K}"))
			sort = "K";
		cellSorts.put(c.getLabel(), sort);
	}

	public static boolean isListSort(String sort) {
		return DefinitionHelper.listConses.containsKey(sort);
	}

	public static void addSubsort(String bigSort, String smallSort) {
		// add the new subsorting
		subsorts.add(new Subsort(bigSort, smallSort));

		// detect if lists are subsorted (Vals Ids < Exps)
		for (Map.Entry<String, Production> ls1 : listConses.entrySet()) {
			for (Map.Entry<String, Production> ls2 : listConses.entrySet()) {
				String sort1 = ((UserList) ls1.getValue().getItems().get(0)).getSort();
				String sort2 = ((UserList) ls2.getValue().getItems().get(0)).getSort();
				if (DefinitionHelper.isSubsorted(sort1, sort2)) {
					subsorts.add(new Subsort(ls1.getValue().getSort(), ls2.getValue().getSort()));
				}
			}
		}

		// closure for sorts
		boolean finished = false;
		while (!finished) {
			finished = true;
			Set<Subsort> ssTemp = new HashSet<Subsort>();
			for (Subsort s1 : subsorts) {
				for (Subsort s2 : subsorts) {
					if (s1.getBigSort().equals(s2.getSmallSort())) {
						Subsort sTemp = new Subsort(s2.getBigSort(), s1.getSmallSort());
						if (!subsorts.contains(sTemp)) {
							ssTemp.add(sTemp);
							finished = false;
						}
					}
				}
			}
			subsorts.addAll(ssTemp);
		}
	}

	public static void addFileRequirement(String required, String local) {
		// add the new subsorting
		fileRequirements.add(new Subsort(required, local));

		// closure for sorts
		boolean finished = false;
		while (!finished) {
			finished = true;
			Set<Subsort> ssTemp = new HashSet<Subsort>();
			for (Subsort s1 : fileRequirements) {
				for (Subsort s2 : fileRequirements) {
					if (s1.getBigSort().equals(s2.getSmallSort())) {
						Subsort sTemp = new Subsort(s2.getBigSort(), s1.getSmallSort());
						if (!fileRequirements.contains(sTemp)) {
							ssTemp.add(sTemp);
							finished = false;
						}
					}
				}
			}
			fileRequirements.addAll(ssTemp);
		}
	}

	public static boolean isRequiredEq(String required, String local) {
		if (required.equals(local))
			return true;
		return fileRequirements.contains(new Subsort(required, local));
	}

	/**
	 * Check to see if smallSort is subsorted to bigSort (strict)
	 * 
	 * @param bigSort
	 * @param smallSort
	 * @return
	 */
	public static boolean isSubsorted(String bigSort, String smallSort) {
		return subsorts.contains(new Subsort(bigSort, smallSort));
	}

	/**
	 * Check to see if smallSort is subsorted or equal to bigSort
	 * 
	 * @param bigSort
	 * @param smallSort
	 * @return
	 */
	public static boolean isSubsortedEq(String bigSort, String smallSort) {
		if (bigSort.equals(smallSort))
			return true;
		return subsorts.contains(new Subsort(bigSort, smallSort));
	}

	public static boolean isTagGenerated(String key) {
		return generatedTags.contains(key);
	}

	public static boolean isSpecialTerminal(String terminal) {
		return specialTerminals.contains(terminal);
	}

	public static boolean isParsingTag(String key) {
		return parsingTags.contains(key);
	}

	public static boolean isListUnit(Constant cst) {
		if (!isListSort(cst.getSort()))
			return false;
		assert (cst.getValue().equals("." + cst.getSort()));
		return true;
	}
}

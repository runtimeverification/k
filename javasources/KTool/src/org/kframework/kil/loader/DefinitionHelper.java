package org.kframework.kil.loader;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Cell;
import org.kframework.kil.Constant;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.UserList;
import org.kframework.utils.Poset;

public class DefinitionHelper {
	public static boolean initialized = false;
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
	public static java.util.Map<String, Set<String>> labels = new HashMap<String, Set<String>>();
	public static java.util.Map<String, Cell> cells = new HashMap<String, Cell>();
	public static java.util.Map<String, String> cellSorts = new HashMap<String, String>();
	public static java.util.Map<String, Production> listConses = new HashMap<String, Production>();
	public static java.util.Map<String, Set<String>> listLabels = new HashMap<String, Set<String>>();
	private static Poset subsorts = new Poset();;
	public static java.util.Set<String> definedSorts = Sort.getBaseSorts();
	private static Poset priorities = new Poset();
	private static Poset modules = new Poset();
	private static Poset fileRequirements = new Poset();
	public static String startSymbolPgm = "K";
	public static File dotk = null;

	static {
		subsorts.addRelation(MetaK.Constants.KList, "K");
		subsorts.addRelation(MetaK.Constants.KList, "KResult");
		subsorts.addRelation("K", "KResult");
		subsorts.addRelation("Map", "MapItem");
		subsorts.addRelation("Set", "SetItem");
		subsorts.addRelation("List", "ListItem");
		subsorts.addRelation("Bag", "BagItem");
	}

	public static void putLabel(Production p, String cons) {
		String label;
		if (!MetaK.isComputationSort(p.getSort()))
			label = p.getLabel();
		else
			label = p.getKLabel();
		Set<String> s = labels.get(label);
		if (s == null)
			labels.put(label, s = new HashSet<String>());
		s.add(cons);
	}

	public static void putListLabel(Production p) {
		String separator = ((UserList) p.getItems().get(0)).getSeparator();
		String label = MetaK.getListUnitLabel(separator);
		Set<String> s = listLabels.get(label);
		if (s == null)
			listLabels.put(label, s = new HashSet<String>());
		s.add(p.getSort());
	}

	public static void addCellDecl(Cell c) {
		cells.put(c.getLabel(), c);

		String sort = subsorts.getMaxim(c.getContents().getSort());
		if (sort.equals(MetaK.Constants.KList))
			sort = "K";
		cellSorts.put(c.getLabel(), sort);
	}

	public static boolean isListSort(String sort) {
		return DefinitionHelper.listConses.containsKey(sort);
	}

	public static void addPriority(String bigPriority, String smallPriority) {
		// add the new priority
		priorities.addRelation(bigPriority, smallPriority);
	}

	public static void finalizePriority() {
		priorities.transitiveClosure();
	}

	/**
	 * Check to see if the two klabels are in the wrong order according to the priority filter.
	 * 
	 * @param klabelParent
	 * @param klabelChild
	 * @return
	 */
	public static boolean isPriorityWrong(String klabelParent, String klabelChild) {
		return priorities.isInRelation(klabelParent, klabelChild);
	}

	public static void addFileRequirement(String required, String local) {
		// add the new subsorting
		if (required.equals(local))
			return;

		fileRequirements.addRelation(required, local);
	}

	public static void finalizeRequirements() {
		fileRequirements.transitiveClosure();
	}

	public static void addModuleImport(String mainModule, String importedModule) {
		// add the new subsorting
		if (mainModule.equals(importedModule))
			return;

		modules.addRelation(mainModule, importedModule);
	}

	public static void finalizeModules() {
		modules.transitiveClosure();
	}

	public static boolean isModuleIncluded(String localModule, String importedModule) {
		return modules.isInRelation(localModule, importedModule);
	}

	public static boolean isModuleIncludedEq(String localModule, String importedModule) {
		if (localModule.equals(importedModule))
			return true;
		return modules.isInRelation(localModule, importedModule);
	}

	public static boolean isRequiredEq(String required, String local) {
		try {
			required = new File(required).getCanonicalPath();
			local = new File(local).getCanonicalPath();
		} catch (IOException e) {
			e.printStackTrace();
		}
		if (required.equals(local))
			return true;
		return fileRequirements.isInRelation(required, local);
	}

	public static void addSubsort(String bigSort, String smallSort) {
		// add the new subsorting
		subsorts.addRelation(bigSort, smallSort);
	}

	public static void finalizeSubsorts() {
		subsorts.transitiveClosure();
		// detect if lists are subsorted (Vals Ids < Exps)
		for (Map.Entry<String, Production> ls1 : listConses.entrySet()) {
			for (Map.Entry<String, Production> ls2 : listConses.entrySet()) {
				String sort1 = ((UserList) ls1.getValue().getItems().get(0)).getSort();
				String sort2 = ((UserList) ls2.getValue().getItems().get(0)).getSort();
				if (DefinitionHelper.isSubsorted(sort1, sort2)) {
					subsorts.addRelation(ls1.getValue().getSort(), ls2.getValue().getSort());
				}
			}
		}
		subsorts.transitiveClosure();
	}

	/**
	 * Check to see if smallSort is subsorted to bigSort (strict)
	 * 
	 * @param bigSort
	 * @param smallSort
	 * @return
	 */
	public static boolean isSubsorted(String bigSort, String smallSort) {
		return subsorts.isInRelation(bigSort, smallSort);
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
		return isSubsorted(bigSort, smallSort);
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

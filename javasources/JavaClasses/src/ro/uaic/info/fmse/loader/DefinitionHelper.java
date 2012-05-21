package ro.uaic.info.fmse.loader;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Production;

public class DefinitionHelper {
	public static String predefinedModules[] = {
		"AUTO-INCLUDED-MODULE",
		"AUTO-INCLUDED-MODULE-SYNTAX",
		"BOOL-HOOKS",
		"BOOL-SYNTAX-HOOKS",
		"BUILTIN-HOOKS",
		"BUILTIN-SYNTAX-HOOKS",
		"FLOAT-HOOKS",
		"FLOAT-SYNTAX-HOOKS",
		"ID-HOOKS",
		"ID-SYNTAX-HOOKS",
		"INT-HOOKS",
		"INT-SYNTAX-HOOKS",
		"K",
		"K-BAG-EXTRAS",
		"K-DESTRUCTORS",
		"K-EQUAL-HOOKS",
		"K-LIST-EXTRAS",
		"K-MAP-EXTRAS",
		"K-RESULT",
		"K-SET-EXTRAS",
		"K-TECHNIQUE",
		"K-WRAPPERS-LABELS",
		"STRING-HOOKS",
		"STRING-SYNTAX-HOOKS",
		"TCP-HOOKS",
		"URIS",
	};
	
	public static String generatedTags[] = {
		"cons",
		"kgeneratedlabel",
		"prefixlabel",
	};
	
	public static java.util.Map<String, Production> conses = new HashMap<String, Production>();
	public static java.util.Map<String, Production> listConses = new HashMap<String, Production>();
	// contains a mapping from listSort to list separator
	public static java.util.Set<Subsort> subsorts = Subsort.getDefaultSubsorts();

	public static boolean isListSort(String sort) {
		return DefinitionHelper.listConses.containsKey(sort);
	}

	public static void addSubsort(String bigSort, String smallSort) {
		// add the new subsorting
		subsorts.add(new Subsort(bigSort, smallSort));

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

	public static boolean isSubsorted(String bigSort, String smallSort) {
		return subsorts.contains(new Subsort(bigSort, smallSort));
	}

	public static boolean isModulePredefined(String string) {
		return (Arrays.binarySearch(predefinedModules, string) >= 0);
	}

	public static boolean isTagGenerated(String key) {
		return (Arrays.binarySearch(generatedTags, key) >= 0);
	}
}

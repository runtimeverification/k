package ro.uaic.info.fmse.loader;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Production;

public class DefinitionHelper {
	public static String generatedTags[] = { "cons", "kgeneratedlabel", "prefixlabel", };

	public static String parsingTags[] = { "bracket", "left", "right" };

	public static String specialTerminals[] = { "(", ")", ",", "[", "]", "{", "}", };

	public static java.util.Map<String, Production> conses = new HashMap<String, Production>();
	public static java.util.Map<String, Production> listConses = new HashMap<String, Production>();
	// contains a mapping from listSort to list separator
	private static java.util.Set<Subsort> subsorts = Subsort.getDefaultSubsorts();
	private static java.util.Set<Subsort> fileRequirements = new HashSet<Subsort>();

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

	public static boolean isSubsorted(String bigSort, String smallSort) {
		return subsorts.contains(new Subsort(bigSort, smallSort));
	}

	public static boolean isSubsortedEq(String bigSort, String smallSort) {
		if (bigSort.equals(smallSort))
			return true;
		return subsorts.contains(new Subsort(bigSort, smallSort));
	}

	public static boolean isTagGenerated(String key) {
		return (Arrays.binarySearch(generatedTags, key) >= 0);
	}

	public static boolean isSpecialTerminal(String terminal) {
		return (Arrays.binarySearch(specialTerminals, terminal) >= 0);
	}

	public static boolean isParsingTag(String key) {
		return Arrays.binarySearch(parsingTags, key) >= 0;
	}
}

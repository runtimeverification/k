package ro.uaic.info.fmse.ca.filters;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Rule;

public abstract class AbstractMappingFilter {
	public LinkedList<HashMap<Integer, Integer>> filter(
			Configuration configuration, Rule rule,
			LinkedList<HashMap<Integer, Integer>> mappings, String side) {
		List<Map<Integer, Integer>> badmaps = new LinkedList<Map<Integer, Integer>>();

		for (Map<Integer, Integer> map : mappings) {
			boolean bad = applyFilterCriteria(configuration, rule, map, side);
			if (bad)
				badmaps.add(map);
		}

		for (Map<Integer, Integer> badm : badmaps) {
			// System.out.println("Removing: " + badm);
			mappings.remove(badm);
		}
		return mappings;
	}

	public abstract boolean applyFilterCriteria(Configuration configuration,
			Rule rule, Map<Integer, Integer> map, String side);
}

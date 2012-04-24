package ro.uaic.info.fmse.main;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;
import ro.uaic.info.fmse.ca.filters.CompletenessFilter;
import ro.uaic.info.fmse.ca.filters.AbstractMappingFilter;
import ro.uaic.info.fmse.ca.filters.OccurenceFilter;
import ro.uaic.info.fmse.ca.filters.StructuralFilter;

public class ConfigurationInferencer {

	private Configuration configuration;

	public ConfigurationInferencer(Configuration configuration) {
		this.configuration = configuration;
	}

	public Rule inferConfigurationForRule(Rule rule) {

		System.out.println(configuration);
		System.out.println(rule);
		
		// detect mappings for rule
		LinkedList<HashMap<Integer, Integer>> lmappings = detectMappings(rule.getLeft());
		LinkedList<HashMap<Integer, Integer>> rmappings = detectMappings(rule.getRight());

		System.out.println("Before: " + lmappings);
//		System.out.println("Before: " + rmappings);

		// apply filters
		CompletenessFilter cfilter = new CompletenessFilter();
		lmappings = acceptFilter(cfilter, rule, lmappings, "left");
		// rmappings = acceptFilter(cfilter, rule, rmappings);

		OccurenceFilter ofilter = new OccurenceFilter();
		lmappings = acceptFilter(ofilter, rule, lmappings, "left");
//		rmappings = acceptFilter(ofilter, rule, rmappings, "right");
		
		StructuralFilter sfilter = new StructuralFilter();
		lmappings = acceptFilter(sfilter, rule, lmappings, "left");
//		rmappings = acceptFilter(sfilter, rule, rmappings, "right");
		
		System.out.println("After: " + lmappings);
//		System.out.println("After: " + rmappings);

//		 System.out.println("====================================");
//		 System.out.println(configuration);
//		 System.out.println(rule);
//		 System.out.println("LEFT: " + lmappings);
//		 System.out.println("RIGHT: " + rmappings);
//		 System.out.println("====================================\n\n\n");

		// TODO: compute the rule
		return rule;
	}

	public LinkedList<HashMap<Integer, Integer>> acceptFilter(AbstractMappingFilter filter, Rule rule,
			LinkedList<HashMap<Integer, Integer>> lmappings, String side) {
		return filter.filter(configuration, rule, lmappings, side);
	}

	public LinkedList<HashMap<Integer, Integer>> detectMappings(List<Node> side) {

//		System.out.println("THELIST: " + side);
		LinkedList<HashMap<Integer, Integer>> mappings = new LinkedList<HashMap<Integer, Integer>>();
		for (Node l : side) {
			List<Integer> ml = configuration.searchIds(l);
//			System.out.println("Search: " + l.getLabel() + " Found: " + ml);
//			System.out.println("Status: " + mappings);
			if (ml != null && ml.size() > 0) {
				if (mappings.size() == 0) {
					for (Integer mli : ml) {
						HashMap<Integer, Integer> newmap = new HashMap<Integer, Integer>();
						newmap.put(l.getID(), mli);
						mappings.add(newmap);
					}
				} else {
					@SuppressWarnings("unchecked")
					LinkedList<HashMap<Integer, Integer>> tempMappings = (LinkedList<HashMap<Integer, Integer>>)mappings.clone();
					mappings.clear();
					
					for (Integer mli : ml) {
						for (HashMap<Integer, Integer> map : tempMappings) {
							@SuppressWarnings("unchecked")
							HashMap<Integer, Integer> tempMap = (HashMap<Integer, Integer>)map.clone();
							tempMap.put(l.getID(), mli);
							mappings.add(tempMap);
						}						
					}
				}
			}
//			System.out.println("MPS: " + mappings + "\n\n");
		}

		return mappings;
	}

	public Configuration getConfiguration() {
		return configuration;
	}
}

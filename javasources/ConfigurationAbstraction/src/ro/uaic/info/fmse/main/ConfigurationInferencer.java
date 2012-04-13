package ro.uaic.info.fmse.main;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;
import ro.uaic.info.fmse.ca.filters.CompletenessFilter;
import ro.uaic.info.fmse.ca.filters.IFilter;

public class ConfigurationInferencer {

	private Configuration configuration;

	public ConfigurationInferencer(Configuration configuration) {
		this.configuration = configuration;
	}

	public Rule inferConfigurationForRule(Rule rule) {

		// detect mappings for rule
		List<Map<Integer, Integer>> mappings = detectMappings(rule);

		System.out.println("Before: " + mappings);
		
		// apply filters
		CompletenessFilter cfilter = new CompletenessFilter();
		mappings = acceptFilter(cfilter, rule, mappings);
	
		System.out.println("After: " + mappings);
		
		
//		System.out.println("====================================");
//		System.out.println(configuration);
//		System.out.println(mappings);
//		System.out.println(rule);
//		System.out.println("====================================\n\n\n");

		
		// TODO: compute the rule
		return rule;
	}

	public List<Map<Integer, Integer>> acceptFilter(IFilter filter, Rule rule, List<Map<Integer, Integer>> mappings)
	{
		return filter.filter(configuration, rule, mappings);
	}
	
	private List<Map<Integer, Integer>> detectMappings(Rule rule) {

		List<Map<Integer, Integer>> mappings = new LinkedList<Map<Integer, Integer>>();
		for (Node l : rule.getLhs()) {
			List<Integer> ml = configuration.searchIds(l);
			if (ml != null) {
				if (mappings.size() == 0) {
					for (Integer mli : ml) {
						HashMap<Integer, Integer> newmap = new HashMap<Integer, Integer>();
						newmap.put(l.getID(), mli);
						mappings.add(newmap);
					}
				} else {
					for (Map<Integer, Integer> map : mappings) {
						for (Integer mli : ml) {
							map.put(l.getID(), mli);
						}
					}
				}
			}
		}

		return mappings;
	}

	public Configuration getConfiguration() {
		return configuration;
	}
}

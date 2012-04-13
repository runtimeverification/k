package ro.uaic.info.fmse.ca.filters;

import java.util.List;
import java.util.Map;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Rule;

public interface IFilter {
	public List<Map<Integer,Integer>> filter(Configuration configuration, Rule rule, List<Map<Integer, Integer>> mappings);
}

package ro.uaic.info.fmse.ca.filters;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;

public class CompletenessFilter implements IFilter{

	@Override
	public List<Map<Integer, Integer>> filter(Configuration configuration,
			Rule rule, List<Map<Integer, Integer>> mappings) {
		
		List<Map<Integer, Integer>> badmaps = new LinkedList<Map<Integer,Integer>>();
		
		for (Map<Integer, Integer> map : mappings)
		{
			boolean bad = false;
			for(Node rnode : rule.getLeft())
			{
				if (!map.containsKey(rnode.getID()))
					bad = true;
			}
			if (bad) badmaps.add(map);
		}
		
		for(Map<Integer, Integer> badm : badmaps)
		{
			System.out.println("Removing: " + badm);
			mappings.remove(badm); 
		}
		return mappings;
	}

}

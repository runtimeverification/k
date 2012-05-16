package ro.uaic.info.fmse.ca.filters;

import java.util.Map;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;

public class CompletenessFilter extends AbstractMappingFilter{

	@Override
	public boolean applyFilterCriteria(Configuration configuration, Rule rule,
			Map<Integer, Integer> map, String side) {

		boolean bad = false;
		
		for(Node rnode : rule.getLeft())
		{
			if (!map.containsKey(rnode.getID()))
				bad = true;
		}
		
		return bad;
	}

}

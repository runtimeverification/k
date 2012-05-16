package ro.uaic.info.fmse.ca.filters;

import java.util.Map;
import java.util.Set;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;

public class StructuralFilter extends AbstractMappingFilter {

	@Override
	public boolean applyFilterCriteria(Configuration configuration, Rule rule,
			Map<Integer, Integer> map, String side) {
		
		for (Node r : rule.getLeft())
		{
			Set<Integer> rAncestors = r.getAncestors();
			Integer cId = map.get(r.getID());
			Node cNode = configuration.searchNode(cId);
			if (cNode == null)
			{
				if (rAncestors.size() > 0)
					return true;
			}
			else {
				Set<Integer> cAncestors = cNode.getAncestors();
				for(Integer id : rAncestors)
					if (!cAncestors.contains(map.get(id)))
						return true;
			}
		}
		
		return false;
	}

}

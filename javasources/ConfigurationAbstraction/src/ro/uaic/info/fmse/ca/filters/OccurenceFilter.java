package ro.uaic.info.fmse.ca.filters;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;

public class OccurenceFilter extends AbstractMappingFilter {

	@Override
	public boolean applyFilterCriteria(Configuration configuration, Rule rule,
			Map<Integer, Integer> map, String side) {
		
		List<Node> list = null;
		if (side.equals("left"))
			list = rule.getLeft();
		else if (side.equals("right"))
			list = rule.getRight();
		else {
			// REPORT ERROR
		}
		
//		System.out.println(rule.getLeft());
		boolean bad = false;
		
		for (Node node : list) {
//			System.out.println(node);
//			System.out.println("FOR: " + map
//					.get(node.getID()) + " Compare: " + configuration.multiplicity(map
//					.get(node.getID())) + " < " + occurence(node, map, rule));
			if (configuration.multiplicity(map
					.get(node.getID())) < occurence(node, map, rule)) {
//				System.out.println("BAD!\n");
				bad = true;
			}
		}

		return bad;
	}

	private Integer occurence(Node node, Map<Integer, Integer> map, Rule rule) {

		int occ = 0;
		Integer cid = map.get(node.getID());
		if (cid != null)
			occ = 1;
		else
			return 0;
		
		for (Entry<Integer, Integer> entry : map.entrySet())
			if (entry.getValue() == cid
					&& rule.siblings(node.getID(), entry.getKey(), "left"))
			{
//				System.out.println("Counting " + entry);
//				System.out.println("For: (" +  node.getID() + ") vs (" + entry.getKey() + ") => " + (rule.siblings(node.getID(), entry.getKey(), "left")));
				occ++;
			}
		return occ;
	}
}

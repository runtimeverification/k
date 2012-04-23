package ro.uaic.info.fmse.tests;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;

import org.junit.Test;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Node;
import ro.uaic.info.fmse.ca.Rule;
import ro.uaic.info.fmse.main.ConfigurationInferencer;

public class CompletenessFilterTests {

	@Test
	public final void testFilter() {

		ro.uaic.info.fmse.tests.Test test = new ro.uaic.info.fmse.tests.Test();
		
		Configuration configuration = test.getConfig();
		Rule rule1 = test.getRule1();
		Rule rule2 = test.getRule2();
		ConfigurationInferencer ci = new ConfigurationInferencer(configuration);
//		System.out.println(configuration);

		List<HashMap<Integer, Integer>> mps1 = ci.detectMappings(rule1.getLeft());
//		System.out.println(rule1);
//		System.out.println(mps);

		boolean ruleOne = false;
		for (Map<Integer, Integer> map : mps1)
		{
			for(Node node : rule1.getLeft())
			{
//				System.out.println("Check " + node + " result: " + map.containsKey(node.getID()));
				if (!map.containsKey(node.getID()))
					ruleOne = true;
			}
		}

		Assert.assertTrue(ruleOne == false);

		List<HashMap<Integer, Integer>> mps2 = ci.detectMappings(rule2.getLeft());
//		System.out.println(rule2);
//		System.out.println(mps2);
		boolean ruleTwo = false;
		for (Map<Integer, Integer> map : mps2)
		{
			for(Node node : rule2.getLeft())
			{
				if (!map.containsKey(node.getID()))
					ruleTwo = true;
			}
		}
		Assert.assertTrue(ruleTwo);

	}

}

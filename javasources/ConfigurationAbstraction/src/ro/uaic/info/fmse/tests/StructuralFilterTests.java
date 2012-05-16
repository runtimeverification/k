package ro.uaic.info.fmse.tests;

// import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.LinkedList;

// import org.junit.Test;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Rule;
import ro.uaic.info.fmse.ca.filters.StructuralFilter;
import ro.uaic.info.fmse.main.ConfigurationInferencer;

public class StructuralFilterTests {

//	@Test
	public final void testApplyFilterCriteria() {
		
		ro.uaic.info.fmse.tests.Test test = new ro.uaic.info.fmse.tests.Test();

		Configuration configuration = test.getConfig();
		ConfigurationInferencer ci = new ConfigurationInferencer(configuration);

		Rule rule1 = test.getRule1();
		LinkedList<HashMap<Integer, Integer>> mps = ci.detectMappings(rule1.getLeft());

//		System.out.println(configuration);
//		System.out.println(rule1);
//		System.out.println(mps);
		StructuralFilter sf = new StructuralFilter();
//		System.out.println(sf.filter(configuration, rule1, mps, "left"));
//		assertTrue(sf.filter(configuration, rule1, mps, "left").toString().equals("[{21=8, 20=3, 23=5, 22=5, 24=19}]"));
	}

}

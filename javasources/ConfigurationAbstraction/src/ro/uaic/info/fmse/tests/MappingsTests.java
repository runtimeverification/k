package ro.uaic.info.fmse.tests;

import java.util.HashMap;
import java.util.List;

import org.junit.Test;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Rule;
import ro.uaic.info.fmse.main.ConfigurationInferencer;

public class MappingsTests {

	@Test
	public final void testDetectMappings() {

		ro.uaic.info.fmse.tests.Test test = new ro.uaic.info.fmse.tests.Test();

		Configuration configuration = test.getConfig();
		ConfigurationInferencer ci = new ConfigurationInferencer(configuration);

		Rule rule1 = test.getRule1();
		List<HashMap<Integer, Integer>> mps = ci.detectMappings(rule1.getLeft());
//		System.out.println(configuration);
//		System.out.println(rule1);
//		System.out.println(mps);

		assert(mps.toString().equals("[{21=7, 20=3, 23=5, 22=5, 24=19}, {21=8, 20=3, 23=5, 22=5, 24=19}, {21=7, 20=3, 23=5, 22=9, 24=19}, {21=8, 20=3, 23=5, 22=9, 24=19}, {21=7, 20=3, 23=9, 22=5, 24=19}, {21=8, 20=3, 23=9, 22=5, 24=19}, {21=7, 20=3, 23=9, 22=9, 24=19}, {21=8, 20=3, 23=9, 22=9, 24=19}]"));

		Rule rule2 = test.getRule2();
		List<HashMap<Integer, Integer>> mps2 = ci.detectMappings(rule2.getLeft());
//		System.out.println(configuration);
//		System.out.println(rule2);
//		System.out.println(mps2);
		assert(mps2.toString().equals("[{21=7, 20=3, 22=5, 24=19}, {21=8, 20=3, 22=5, 24=19}, {21=7, 20=3, 22=9, 24=19}, {21=8, 20=3, 22=9, 24=19}]"));
	}
}

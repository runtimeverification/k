package ro.uaic.info.fmse.tests;

import java.util.HashMap;
import java.util.LinkedList;

import junit.framework.Assert;

import org.junit.Test;

import ro.uaic.info.fmse.ca.Configuration;
import ro.uaic.info.fmse.ca.Rule;
import ro.uaic.info.fmse.ca.filters.OccurenceFilter;
import ro.uaic.info.fmse.main.ConfigurationInferencer;

public class OccurenceFilterTests {

	@Test
	public final void test() {
		ro.uaic.info.fmse.tests.Test test = new ro.uaic.info.fmse.tests.Test();

		Configuration configuration = test.getConfig();
		ConfigurationInferencer ci = new ConfigurationInferencer(configuration);

		Rule rule1 = test.getRule1();
		LinkedList<HashMap<Integer, Integer>> mps = ci.detectMappings(rule1.getLeft());
		
//		System.out.println(configuration);
//		System.out.println(rule1);
//		System.out.println("H:" + mps);
		
		OccurenceFilter of = new OccurenceFilter();
		Assert.assertTrue(of.filter(configuration, rule1, mps, "left").toString().equals("[{21=7, 20=3, 23=5, 22=5, 24=19}, {21=8, 20=3, 23=5, 22=5, 24=19}, {21=7, 20=3, 23=5, 22=9, 24=19}, {21=8, 20=3, 23=5, 22=9, 24=19}, {21=7, 20=3, 23=9, 22=5, 24=19}, {21=8, 20=3, 23=9, 22=5, 24=19}]"));
	}

}

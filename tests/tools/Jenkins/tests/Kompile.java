import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.junit.Test;

public class Kompile {

	@Test
	public void kompile() throws InterruptedException, URISyntaxException {
		System.out.println("\nCompiling examples...");
		
		// Check the existence of the configuration file
		String configuration = StaticK.configuration;
		if (!new File(configuration).exists()){
			System.out.println("INTERNAL JENKINS ERROR: " + new File(configuration).getAbsolutePath() + " doesn't exists.");
			System.exit(1);
		}
		
		// collecting examples to be compiled
		List<Example> examples = StaticK.getExamples(configuration, StaticK.k3Jar, "example", StaticK.kbasedir);
		List<Example> regression = StaticK.getExamples(configuration, StaticK.k3Jar, "regression", StaticK.kbasedir);
		List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
		
		for (Example example : examples)
			tasks.add(Executors.callable(example));
		for (Example r : regression)
			tasks.add(Executors.callable(r));
		
		ExecutorService es = Executors.newFixedThreadPool(StaticK.initPoolSize());
		es.invokeAll(tasks);
		
		// create reports
		for (Example example : examples) {
			String jdir = StaticK.kbasedir + StaticK.fileSep + "junit-reports";
			
			if (!new File(jdir).exists())
				{new File(jdir).mkdir();}
			
			String file = jdir + StaticK.fileSep + example.getJenkinsSuiteName().replaceAll("[\\/:]+", "") + ".xml";
			Report report = new Report(file, "examples", example.getJenkinsSuiteName());
			report.report(example);
			report.save();
			StaticK.reports.put(example.getJenkinsSuiteName(), report);
		}

		for (Example r : regression) {
			String jdir = StaticK.kbasedir + StaticK.fileSep + "junit-reports";
			
			if (!new File(jdir).exists())
				new File(jdir).mkdir();
			
			String file = jdir + StaticK.fileSep + r.getJenkinsSuiteName().replaceAll("[\\/:]+", "") + ".xml";
			Report report = new Report(file, "regression", r.getJenkinsSuiteName());
			report.report(r);
			report.save();
			StaticK.reports.put(r.getJenkinsSuiteName(), report);
		}

		
		
		// assert now...
		for (Example example : examples) {
			assertTrue(example.isCompiled());
		}

		for (Example r : regression) {
			assertTrue(r.isCompiled());
		}

		System.out.println("\nDone.");
	}

}

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;
import java.util.List;

import org.junit.Test;

public class Kompile {

	@Test
	public void kompile() throws InterruptedException, URISyntaxException {
		System.out.println("\nCompiling examples...");
		
		String configuration = StaticK.configuration;
		assertTrue(new File(configuration).exists());

		
		List<Example> examples = StaticK.getExamples(configuration, StaticK.k3Jar, "example", StaticK.kbasedir);
		List<Example> regression = StaticK.getExamples(configuration, StaticK.k3Jar, "regression", StaticK.kbasedir);

		for (Example example : examples)
			example.start();
		for (Example r : regression)
			r.start();
		
		// report first
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

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.LinkedList;
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
		if (!new File(configuration).exists()) {
			System.out.println("INTERNAL JENKINS ERROR: "
					+ new File(configuration).getAbsolutePath()
					+ " doesn't exists.");
			System.exit(1);
		}

		List<Callable<Object>> tasks = new ArrayList<Callable<Object>>();
		List<List<Example>> all = new LinkedList<List<Example>>();

		// collecting examples to be compiled
		for (String ert : StaticK.tags) {
			List<Example> es = StaticK.getExamples(configuration,
					StaticK.k3Jar, ert, StaticK.kbasedir);
			for (Example e : es)
				tasks.add(Executors.callable(e));
			all.add(es);
		}

		ExecutorService es = Executors.newFixedThreadPool(StaticK
				.initPoolSize());
		es.invokeAll(tasks);

		// create reports
		for (String ert : StaticK.tags) {
			for (Example example : all.get(StaticK.tags.indexOf(ert))) {
				String jdir = StaticK.kbasedir + StaticK.fileSep
						+ "junit-reports";

				if (!new File(jdir).exists()) {
					new File(jdir).mkdir();
				}

				String file = jdir
						+ StaticK.fileSep
						+ example.getJenkinsSuiteName().replaceAll("[\\/:]+",
								"") + ".xml";
				Report report = new Report(file, "examples",
						example.getJenkinsSuiteName());
				report.report(example);
				report.save();
				StaticK.reports.put(example.getJenkinsSuiteName(), report);
			}
		}

		// assert now...
		for (List<Example> examples : all)
			for (Example example : examples) {
				assertTrue(example.isCompiled());
			}

		System.out.println("\nDone.");
	}

}

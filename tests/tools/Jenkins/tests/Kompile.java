import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

import org.junit.Test;

public class Kompile {

	@Test
	public void kompile() throws InterruptedException, URISyntaxException {
		System.out.println("\nCompiling examples...");
		
		String configuration = StaticK.configuration;
		assertTrue(new File(configuration).exists());

		
		List<Example> examples = StaticK.getExamples(configuration, StaticK.k3Jar, "example", StaticK.kbasedir);
		List<Example> regression = StaticK.getExamples(configuration, StaticK.k3Jar, "regression", StaticK.kbasedir);
		StaticK.pool = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(StaticK.THREAD_POOL_SIZE);

		for (Example example : examples)
			StaticK.pool.execute(example);
		for (Example r : regression)
			StaticK.pool.execute(r);

		
		// wait until examples are running
		while (StaticK.pool.getCompletedTaskCount() != (examples.size() + regression.size())) {
			Thread.sleep(1);
		}
		
		for (Example example : examples) {
			StaticK.report.report(example);
			assertTrue(example.isCompiled());
		}

		for (Example r : regression) {
			StaticK.report.report(r);
			assertTrue(r.isCompiled());
		}
		
		StaticK.report.save();
		System.out.println("\nDone.");
	}

}

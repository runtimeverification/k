import static org.junit.Assert.assertTrue;

import java.net.URISyntaxException;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

import org.junit.Test;


public class Kompile {

	@Test
	public void kompile() throws InterruptedException, URISyntaxException {
		System.out.println("\nCompiling examples...");
		String configuration = StaticK.file.getAbsolutePath().replaceFirst(
				"/Jenkins.*?$", "")
				+ StaticK.fileSep + "configuration.xml";
		List<Example> examples = StaticK.getExamples(configuration, StaticK.k3Jar);
		StaticK.pool = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(StaticK.THREAD_POOL_SIZE);
		for (Example example : examples)
			StaticK.pool.execute(example);

		// wait until examples are running
		while (StaticK.pool.getCompletedTaskCount() != examples.size()) {
			Thread.sleep(1);
		}

		for (Example example : examples) {
			assertTrue(example.isCompiled());
		}
		
		System.out.println("\nDone.");
	}

}

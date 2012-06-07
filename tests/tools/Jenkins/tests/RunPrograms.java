import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

import org.junit.Test;


public class RunPrograms {

	@Test
	public void runPrograms() throws InterruptedException {
		System.out.println("\nRunning programs...");
		String configuration = StaticK.file.getAbsolutePath().replaceFirst(
				"/Jenkins.*?$", "")
				+ StaticK.fileSep + "configuration.xml";
		List<Example> examples = StaticK.getExamples(configuration, StaticK.k3Jar);
		StaticK.pool = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(StaticK.THREAD_POOL_SIZE);
		for (Example example : examples)
		{
			example.runPrograms = true;
			StaticK.pool.execute(example);
		}
		// wait until examples are running
		while (StaticK.pool.getCompletedTaskCount() != examples.size()) {
			Thread.sleep(1);
		}

//		for (Example example : examples) {
//			assertTrue(example.isCompiled());
//		}
//		
		System.out.println("\nDone.");
	}

}

import static org.junit.Assert.assertTrue;

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
				+ StaticK.fileSep + "Jenkins" + StaticK.fileSep + "configuration.xml";
		List<Example> examples = StaticK.getExamples(configuration, StaticK.k3Jar, "example");
		List<Example> regression = StaticK.getExamples(configuration, StaticK.k3Jar, "regression");
		
		
		StaticK.pool = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(StaticK.THREAD_POOL_SIZE);
		for (Example example : examples)
		{
			example.runPrograms = true;
			StaticK.pool.execute(example);
		}
		for (Example example : regression)
		{
			example.runPrograms = true;
			StaticK.pool.execute(example);
		}

		// wait until examples are running
		while (StaticK.pool.getCompletedTaskCount() != examples.size() + regression.size()) {
			Thread.sleep(1);
		}

		
		for(Example example : examples)
		{
			for(Program program : example.programs)
			{
				StaticK.report.report(program, example.getFile().replaceAll("\\..*?$", "") + " programs");
			}
			StaticK.report.save();
		}
		for(Example example : regression)
		{
			for(Program program : example.programs)
			{
				StaticK.report.report(program, example.getFile().replaceAll("\\..*?$", "") + " programs");
			}
			StaticK.report.save();
		}

		for(Example example : examples)
		{
			for(Program program : example.programs)
			{
				assertTrue(program.isCorrect());
			}
		}
		for(Example example : regression)
		{
			for(Program program : example.programs)
			{
				assertTrue(program.isCorrect());
			}
		}

		System.out.println("\nDone.");
	}

}

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

import org.junit.Test;

public class RunPrograms {

	@Test
	public void runPrograms() throws InterruptedException {
		System.out.println("\nRunning programs...");
		String configuration = StaticK.configuration;
		
		assertTrue(new File(configuration).exists());
		
		List<Example> examples = StaticK.getExamples(configuration, StaticK.k3Jar, "example", StaticK.kbasedir);
		List<Example> regression = StaticK.getExamples(configuration, StaticK.k3Jar, "regression", StaticK.kbasedir);
		
		
		ThreadPoolExecutor pool = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(StaticK.initPoolSize());
		for (Example example : examples)
		{
			example.runPrograms = true;
			pool.execute(example);
		}
		for (Example example : regression)
		{
			example.runPrograms = true;
			pool.execute(example);
		}

		// wait until examples are running
		while (pool.getCompletedTaskCount() != examples.size() + regression.size()) {
			Thread.sleep(1);
		}

		pool.shutdown();
		
		for(Example example : examples)
		{
			Report report = StaticK.reports.get(example.getJenkinsSuiteName());
			for(Program program : example.programs)
			{
				report.report(program);
			}
			report.save();
			StaticK.reports.put(example.getJenkinsSuiteName(), report);
		}
		
		for(Example r : regression)
		{
			Report report = StaticK.reports.get(r.getJenkinsSuiteName());
			for(Program program : r.programs)
			{
				report.report(program);
			}
			report.save();
			StaticK.reports.put(r.getJenkinsSuiteName(), report);
		}

		for(Example example : examples)
		{
			for(Program program : example.programs)
			{
				assertTrue(program.isCorrect());
			}
		}
		for(Example r : regression)
		{
			for(Program program : r.programs)
			{
				assertTrue(program.isCorrect());
			}
		}

		System.out.println("\nDone.");
	}

}

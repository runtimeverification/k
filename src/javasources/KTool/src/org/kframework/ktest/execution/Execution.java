package org.kframework.ktest.execution;

import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import org.kframework.ktest.Configuration;

public class Execution {
	public static int POOL_SIZE = initPoolSize(Runtime.getRuntime()
			.availableProcessors());
	public static ThreadPoolExecutor tpe = getThreadPoolExecutor();

	private static ThreadPoolExecutor getThreadPoolExecutor() {
		return (ThreadPoolExecutor) Executors
				.newFixedThreadPool(POOL_SIZE);
	}

	public static void execute(Task definitionTask) {
		tpe.execute(definitionTask);
	}

	public static void finish() { 
		// wait for tasks to finish
		try {
			Execution.tpe.shutdown();
			Execution.tpe.awaitTermination(Configuration.KOMPILE_ALL_TIMEOUT,
					TimeUnit.SECONDS);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		Execution.tpe.shutdownNow();
		Execution.tpe = getThreadPoolExecutor();
	}

	public static int initPoolSize(int cores) {
		int poolSize = 1;
		int pS = cores;// - cores / 4;
		if (pS > poolSize)
			return pS;

		return poolSize;
	}
}

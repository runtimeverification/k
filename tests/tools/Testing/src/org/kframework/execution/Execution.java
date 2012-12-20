package org.kframework.execution;

import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import org.kframework.main.Configuration;


public class Execution {
	public static int SIZE = initPoolSize();
	public static ThreadPoolExecutor tpe = (ThreadPoolExecutor) Executors.newFixedThreadPool(SIZE);
	
	public static void execute(Task definitionTask) {
		tpe.execute(definitionTask);
	}

	public static void finish()
	{		// wait for definitions to finish
		try{
			Execution.tpe.shutdown();
			Execution.tpe.awaitTermination(Configuration.KOMPILE_ALL_TIMEOUT, TimeUnit.MINUTES);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		Execution.tpe.shutdownNow();
		Execution.tpe = (ThreadPoolExecutor) Executors.newFixedThreadPool(SIZE);
	}
	
	public static int initPoolSize()
    {
            int poolSize = 1;
            int cores = Runtime.getRuntime().availableProcessors();
            int pS = cores;// - cores / 4;
            if (pS > poolSize)
                    return pS;
            
            return poolSize;
    }
}

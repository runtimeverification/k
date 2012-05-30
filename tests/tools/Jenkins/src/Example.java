

import java.io.File;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

public class Example extends Thread{
	String dir;
	String mainFile;
	String compiledFile;
	String mainModule;
	String[] krunOptions;
	String k3jar;
	List<Program> programs;
	String output = "", error = "";
	int exitCode;
	long millis;
	private int THREAD_POOL_SIZE = 24;
	
	public Example(String dir, String mainFile, String mainModule,
			String[] krunOptions, String k3jar, String compiledFile,
			List<Program> programs) {
		super();
		this.dir = dir;
		this.mainFile = mainFile;
		this.mainModule = mainModule;
		this.krunOptions = krunOptions;
		this.k3jar = k3jar;
		this.programs = programs;
		this.compiledFile = compiledFile;
	}


	@Override
	public void run() {
		
		// compile the definition: java -ss8m -Xms64m -Xmx1G  -jar
		long millis = System.currentTimeMillis();
		Executor compile = new Executor(new String[]{ "java", "-ss8m", "-Xms64m", "-Xmx1G", "-jar", k3jar, "-kompile", mainFile, "-l", mainModule}, dir);
//		String kompile = new File(k3jar).getAbsolutePath().replaceFirst("/java.*?$", "") + System.getProperty("file.separator") + "kompile";
//		Executor compile = new Executor(new String[]{ "bash" ,kompile, mainFile, "-l", mainModule}, dir);
		ThreadPoolExecutor tpe = (ThreadPoolExecutor) Executors.newFixedThreadPool(THREAD_POOL_SIZE);
		tpe.execute(compile);
		while(tpe.getCompletedTaskCount() != 1)
		{
			try {
				Thread.sleep(1);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		output = compile.getOutput();
		error = compile.getError();
		exitCode = compile.getExitValue();
		this.millis = System.currentTimeMillis() - millis;
		System.out.println(this);
	}
	
	@Override
	public String toString() {
		return "Testing " + mainFile;// + ":\nCompilation status: " + exitCode + "\nOutput: " + output + "\nError: " + error + "\n" + "Compile time: " + millis + " milliseconds.\n";
	}


	public boolean isCompiled() {
		return new File(dir + System.getProperty("file.separator") + compiledFile).exists();
	}
}

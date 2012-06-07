import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;



public class Program extends Thread{
	public String filename, inputFile, outputFile, krun, kdefinition, dir;

	public Program(String filename, String inputFile, String outputFile,
			String krun, String kdefinition, String dir) {
		super();
		this.filename = filename;
		this.inputFile = inputFile;
		this.outputFile = outputFile;
		this.krun = krun;
		this.kdefinition = kdefinition;
		this.dir = dir;
	}
	
	@Override
	public void run() {
		super.run();
		
		Executor compile = new Executor(new String[] { "java", "-jar" , krun, filename,
				"--k-definition", kdefinition }, dir);
		ThreadPoolExecutor tpe = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(StaticK.THREAD_POOL_SIZE);
		tpe.execute(compile);
		while (tpe.getCompletedTaskCount() != 1) {
			try {
				Thread.sleep(1);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		String output = compile.getOutput();
		String error = compile.getError();
		int exitCode = compile.getExitValue();
		System.out.println(filename + "\nOut: " + output + "\nError: " + error + "\nExit: " + exitCode);
	}
	
	
	@Override
	public String toString() {
		return "Testing " + filename + " ... ";
	}
}

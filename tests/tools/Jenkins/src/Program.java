import java.io.File;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

public class Program extends Thread {
	public String filename, inputFile, outputFile, krun, kdefinition, dir;

	private String output = "", error = "";
	private int exit;
	private Executor compile;
	
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

		compile = new Executor(new String[] { "java", "-jar", krun,
					filename, "--k-definition", kdefinition , "--output-mode", "none"}, dir, StaticK.readFileAsString(inputFile));
		ThreadPoolExecutor tpe = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(StaticK.THREAD_POOL_SIZE);
		tpe.execute(compile);
		compile.start();
		while (tpe.getCompletedTaskCount() != 1) {
			try {
				Thread.sleep(1);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		output = compile.getOutput();
		error = compile.getError();
		exit = compile.getExitValue();
	}

	public boolean isCorrect() {
		if (outputFile.equals("") || new File(outputFile).isDirectory())
			if (exit == 0)
				return true;
			else return false;

		if (new File(outputFile).exists())
		{
			String out = StaticK.readFileAsString(new File(outputFile)
			.getAbsolutePath());
			if (out.trim().equals(output.trim()) && exit == 0)
				return true;
		}
		else {
			System.out.println("\t\tINTERNAL ERROR: output file (" + outputFile + ") for program (" +  filename + ") does not exist.");
			System.exit(2);
		}
		return false;
	}

	@Override
	public String toString() {
		if (isCorrect())
			return filename + "... success.";
		else return filename + " ... failed:\n\n------------ STATS ------------\nRun:\n" + compile + "\nKrun exit code: " + exit + "\nError: " + error + "\nOutput: " + output + "\n-------------------------------\n";
	}
}

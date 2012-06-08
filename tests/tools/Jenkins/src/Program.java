import java.io.File;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

public class Program extends Thread {
	public String filename, inputFile, outputFile, krun, kdefinition, dir;

	private String output = "", error = "";
	private int exit;

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

		Executor compile;
//		if (new File(inputFile).exists())
//			compile = new Executor(new String[] { "cat", inputFile, "|",
//					"java", "-jar", krun, filename, "--k-definition",
//					kdefinition }, dir);
//		else
			compile = new Executor(new String[] { "java", "-jar", krun,
					filename, "--k-definition", kdefinition , "--output-mode", "none"}, dir);
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

		output = compile.getOutput();
		error = compile.getError();
		exit = compile.getExitValue();
//		System.out.println(filename + "\nOut: " + output + "\nError: " + error
//				+ "\nExit: " + exit);
	}

	public boolean isCorrect() {
		
		System.out.println(filename + "\nOut: " + output + "\nError: " + error
				+ "\nExit: " + exit);
		if (!new File(outputFile).exists()) {
			if (error.equals("") && exit == 0)
				return true;
		} else {
			String out = StaticK.readFileAsString(new File(outputFile)
					.getAbsolutePath());
			System.out.println("Comparing: ");
			System.out.println("1|" + out + "|1");
			System.out.println("2|" + output + "|3");
			System.out.println("END");
			if (out.trim().equals(output.trim()) && exit == 0)
				return true;
		}
		return false;
	}

	@Override
	public String toString() {
		return "Testing " + filename + " ... ";
	}
}

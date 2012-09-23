import java.io.File;
import java.util.List;

public class Program extends Thread {
	public String filename, inputFile, outputFile, krun, kdefinition, dir;
	public List<String> krunOptions;

	private String output = "", error = "", sent = "";
	private int exit;
	private Executor compile;
	private long time = 0;
	public String type = "";
	private boolean timedout = false;
	
	public Program(String filename, String inputFile, String outputFile,
			String krun, String kdefinition, String dir,
			List<String> krunOptions, String type) {
		super();
		this.filename = filename;
		this.inputFile = inputFile;
		this.outputFile = outputFile;
		this.krun = krun;
		this.kdefinition = kdefinition;
		this.dir = dir;
		this.krunOptions = krunOptions;
		this.type = type;
	}

	@Override
	public void run() {
		super.run();

		long millis = System.currentTimeMillis();
		
		/* Compute the krun arguments */
		String[] basic = new String[] { "java", "-ss8m", "-Xms64m", "-Xmx1G", "-jar", krun, "-krun", filename,
				"--k-definition", kdefinition, " --no-deleteTempDir" };
		int length = basic.length + krunOptions.size();
		String[] run = new String[length];
		for (int i = 0; i < length; i++)
			if (i < basic.length)
				run[i] = basic[i];
		int i = 0;
		for (String opt : krunOptions) {
			run[i + basic.length] = opt;
			i++;
		}
		/* END */

		compile = new Executor(run, dir, StaticK.readFileAsString(inputFile));
		compile.start();

		try {
			compile.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		output = compile.getOutput();
		error = compile.getError();
		exit = compile.getExitValue();
		timedout = compile.getTimedOut();
		time = System.currentTimeMillis() - millis;
		sent = compile.sent;
	}

	public boolean isCorrect() {
		if (timedout)
			return false;
		
		if (outputFile.equals("") || new File(outputFile).isDirectory())
			if (exit == 0)
				return true;
			else
				return false;

		if (new File(outputFile).exists()) {
			String out = StaticK.readFileAsString(new File(outputFile)
					.getAbsolutePath());
			if (out.trim().equals(output.trim()) && exit == 0)
				return true;
		} else {
			System.out.println("\t\tINTERNAL ERROR: output file (" + outputFile
					+ ") for program (" + filename + ") does not exist.");
			System.exit(2);
		}
		return false;
	}

	@Override
	public String toString() {
		String expected = StaticK.readFileAsString(outputFile);
		String input = StaticK.readFileAsString(inputFile);

		if (isCorrect())
			return filename.substring(StaticK.kbasedir.length()) + "... success.";
		else
			return filename.substring(StaticK.kbasedir.length())
					+ "... failed:\n\n------------ STATS ------------\nRun:\n"
					+ compile + "\nKrun exit code: " + exit + "\nError: "
					+ error + "\nOutput: |" + output
					+ "|\nExpecting: |" + expected
					+ "|\nInput: |" + input
					+ "|\nInput file: " + inputFile 
					+ "\nOutput file: " + outputFile
					+ "\nSent: " + sent
					+ "\n-------------------------------\n";
	}

	public long getTime() {
		return time;
	}
	
	public String getOutput()
	{
		return output;
	}
	
	public String getError()
	{
		return error;
	}
}

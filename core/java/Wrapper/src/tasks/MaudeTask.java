package tasks;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.OutputStreamWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

public class MaudeTask extends Task {
	private static final String LOG_FILE = "maude.log";
	private static final String LOGGER = "maude";
	private Logger _logger;
	private String _maudeFile;
	private String _outputFile;

	public MaudeTask(String cmd, String maudeFile, String outputFile, Logger parentLogger) {
		super(cmd);
		_maudeFile = maudeFile;
		_outputFile = outputFile;

		// init logger
		// try {
			// boolean append = true;
			// FileHandler fh = new FileHandler(LOG_FILE, append);
			// fh.setFormatter(new SimpleFormatter());
			// logger = java.util.logging.Logger.getLogger(LOGGER);
			// logger.setParent(parentLogger);
			// logger.addHandler(fh);
			// logger.setUseParentHandlers(false);
		_logger = parentLogger;
		// } catch (IOException e) {
			// e.printStackTrace();
		// }
	}

	@Override
	public void run() {
		try {
			ProcessBuilder maude = new ProcessBuilder();
			
			List<String> commands = new ArrayList<String>();
			commands.add(cmd);
			commands.add("-no-wrap");
			commands.add("-no-banner");
			commands.add(_maudeFile);
			maude.command(commands);
//			maude.environment().put("MAUDE_LIB", "/usr/local/bin/maudeDarwin/maude");
//			maude.environment().put("PATH", maude.environment().get("PATH") + ":/usr/local/bin/maudeDarwin/maude/maude");
			
			Process maudeProcess = maude.start();
			// System.out.println("running maude");
			// redirect out in log file
			BufferedReader maudeOutput = new BufferedReader(new InputStreamReader(maudeProcess.getInputStream()));
			BufferedWriter outputFile = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(_outputFile)));
			
			String line;
			while ((line = maudeOutput.readLine()) != null) {
				// System.out.println(line);
				outputFile.write(line + "\n");
			}
			outputFile.close();

			maudeProcess.waitFor();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}

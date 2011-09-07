package tasks;

import java.io.BufferedReader;
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
	private Logger logger;
	private String file;

	public MaudeTask(String cmd, String file) {

		super(cmd);
		this.file = file;

		// init logger
		try {
			boolean append = true;
			FileHandler fh = new FileHandler(LOG_FILE, append);
			// fh.setFormatter(new XMLFormatter());
			fh.setFormatter(new SimpleFormatter());
			logger = java.util.logging.Logger.getLogger(LOGGER);
			logger.addHandler(fh);
			logger.setUseParentHandlers(false);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void run() {

		try {
			
			ProcessBuilder maude = new ProcessBuilder();
			
			List<String> commands = new ArrayList<String>();
			commands.add(cmd);
			commands.add("-no-wrap");
			commands.add(file);
			maude.command(commands);
//			maude.environment().put("MAUDE_LIB", "/usr/local/bin/maudeDarwin/maude");
//			maude.environment().put("PATH", maude.environment().get("PATH") + ":/usr/local/bin/maudeDarwin/maude/maude");
			
			Process maudeProcess = maude.start();
			
			// redirect out in log file
			BufferedReader stdout = new BufferedReader(new InputStreamReader(
					maudeProcess.getInputStream()));
			String line;
			while ((line = stdout.readLine()) != null) {
				logger.info(line);
			}

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

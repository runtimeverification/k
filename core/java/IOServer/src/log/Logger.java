package log;

import java.io.IOException;
import java.util.logging.FileHandler;
import java.util.logging.SimpleFormatter;

public class Logger {

	public static java.util.logging.Logger logger;
	public static String LOG_FILE = "log_k_IOserver.log";
	public static String LOGGER = "KIO";
	static {
	    try {
	      boolean append = true;
	      FileHandler fh = new FileHandler(LOG_FILE, append);
	      //fh.setFormatter(new XMLFormatter());
	      fh.setFormatter(new SimpleFormatter());
	      logger = java.util.logging.Logger.getLogger(LOGGER);
	      logger.addHandler(fh);
	      logger.setUseParentHandlers(false);
	    }
	    catch (IOException e) {
	      e.printStackTrace();
	    }
	}
	
	public static void info(String info)
	{
		logger.info(info);
	}
	
	public static void severe(String severe)
	{
		logger.severe(severe);
	}
	
	public static void warning(String warning)
	{
		logger.warning(warning);
	}
}

// make && java -jar wrapperAndServer.jar --maudefile blah
package runner;

import java.io.IOException;
import java.util.List;
import java.io.File;
import java.text.MessageFormat;

import main.MainServer;
import tasks.MaudeTask;

import joptsimple.OptionException;
import joptsimple.OptionParser;
import joptsimple.OptionSet;
import joptsimple.OptionSpec;

import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

public class KRunner {
	//private String _maudeCommand = "maude";
	private OptionParser _parser = new OptionParser();
	private Logger _logger;
	
	private File _maudeFile;
	private String _maudeFileName;
	private File _maudeCommandFile;
	private String _maudeCommandFileName;
	private int _port;
	private boolean _append;
	private String _outputFileName;
	private String _errorFileName;
	private String _maudeModule;
	private boolean _createLogs;
	
	
	public KRunner(String[] args) throws Exception, IOException {
		//boolean append = true;
		// parser.accepts("suppressio");
		
		OptionSpec<File> maudeFile = _parser.accepts("maudeFile", "Maude file to run").withRequiredArg().required().ofType(File.class);
		OptionSpec<Integer> port = _parser.accepts("port", "Port to use for IO server").withRequiredArg().ofType(Integer.class).defaultsTo(0);
		OptionSpec<Boolean> append = _parser.accepts("appendLogs", "Whether or not messages should be appended to log files").withRequiredArg().ofType(Boolean.class).defaultsTo(false);
		OptionSpec<File> outputFile = _parser.accepts("outputFile", "File to save resulting term").withRequiredArg().required().ofType(File.class);
		OptionSpec<File> errorFile = _parser.accepts("errorFile", "File to save any Maude errors").withRequiredArg().required().ofType(File.class);
		OptionSpec<File> maudeCommandFile = _parser.accepts("commandFile", "File containing maude command").withRequiredArg().required().ofType(File.class);
		OptionSpec<String> maudeModuleName = _parser.accepts("moduleName", "Final module name").withRequiredArg().required().ofType(String.class);
		OptionSpec<Void> createLogs = _parser.accepts("createLogs", "Create runtime log files");

		OptionSet options;
		try {
			options = _parser.parse(args);
			_maudeFile = options.valueOf(maudeFile);
			_maudeFileName = _maudeFile.getCanonicalPath();
			_maudeCommandFile = options.valueOf(maudeCommandFile);
			_maudeCommandFileName = _maudeCommandFile.getCanonicalPath();
			_port = options.valueOf(port);
			_append = options.valueOf(append);
			_outputFileName = options.valueOf(outputFile).getCanonicalPath();
			_errorFileName = options.valueOf(errorFile).getCanonicalPath();
			_maudeModule = options.valueOf(maudeModuleName);
			_createLogs = options.has(createLogs);
		} catch (OptionException e) {
			System.out.println(e.getMessage() + "\n");
			usageError();
		}
		
		startLogger();
		
		if (!_maudeFile.exists()) {
			throw new Exception("Maude file " + _maudeFileName + " does not exist.");
		}
		if (!_maudeCommandFile.exists()) {
			throw new Exception("Command file " + _maudeCommandFileName + " does not exist.");
		}
		_logger.info("Maude and command files exist.");
	}
	
	private void startLogger() throws IOException {
		_logger = java.util.logging.Logger.getLogger("KRunner");
		if (_createLogs) {
			FileHandler fh = new FileHandler("krunner.log", _append);
			fh.setFormatter(new SimpleFormatter());
			_logger.addHandler(fh);
		}
		_logger.setUseParentHandlers(false);
	}
	
	Thread startServer() {
		_logger.info("Trying to start server on port " + _port);
		MainServer server = new MainServer(_port, _logger);
		Thread t = new Thread(server);
		t.start();
		while (!server._started) {
			Thread.yield();
			// Thread.sleep(500);
		}
		_port = server._port; // in case port was set by server 
		_logger.info("Server started on port " + _port);
		return t;
		// Client.main(null);
	}

	public void run() throws Exception {
		Thread server = startServer();
		
		String commandTemplate = 
			"load {0}\n"
			+ "mod KRUNNER is including {1} .\n"
			+ "eq #TCPPORT = {2,number,#} .\n"
			+ "endm\n"
			+ "load {3}\n"
			;
		String command = MessageFormat.format(commandTemplate, _maudeFileName, _maudeModule, _port, _maudeCommandFileName);
		Thread maude = new MaudeTask(command, _outputFileName, _errorFileName, _logger);
		
		maude.start();
		_logger.info("Maude started");
		_logger.info("Maude command:\n" + command);
		
		maude.join();
		
		System.exit(0);
	}
	
	public static void main(String[] args) throws IOException, Exception {
		KRunner runner = new KRunner(args);
		// try {
		runner.run();
		// } catch (IOException e) {
			// // TODO Auto-generated catch block
			// e.printStackTrace();
		// } catch (InterruptedException e) {
			// // TODO Auto-generated catch block
			// e.printStackTrace();
		// } catch (Exception e) {
			// // TODO Auto-generated catch block
			// e.printStackTrace();
		// }
	}
	
	void usageError() throws IOException {
		_parser.printHelpOn(System.out);
		System.out.println("");
		System.exit(1);
	}
}

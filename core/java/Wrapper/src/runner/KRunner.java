// make && java -jar wrapperAndServer.jar --maudefile blah
package runner;

import java.io.IOException;
import java.util.List;
import java.io.File;

import main.MainServer;
import tasks.MaudeTask;
import tasks.Task;

import joptsimple.OptionException;
import joptsimple.OptionParser;
import joptsimple.OptionSet;
import joptsimple.OptionSpec;

import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

public class KRunner {
	private String _maudeCommand = "maude";
	private OptionParser _parser = new OptionParser();
	private Logger _logger;
	
	private String _maudeFile;
	private int _port;
	private boolean _append;
	private String _outputFile;
		
	public KRunner(String[] args) throws IOException {
		//boolean append = true;
		// parser.accepts("suppressio");
		
		OptionSpec<String> maudefile = _parser.accepts("maudefile", "Maude file to run").withRequiredArg().required().ofType(String.class);
		OptionSpec<Integer> port = _parser.accepts("port", "Port to use for IO server").withRequiredArg().ofType(Integer.class).defaultsTo(0);
		OptionSpec<Boolean> append = _parser.accepts("appendLogs", "Whether or not messages should be appended to log files").withRequiredArg().ofType(Boolean.class).defaultsTo(false);
		OptionSpec<String> outputFile = _parser.accepts("outputfile", "File to save resulting term").withRequiredArg().required().ofType(String.class);

		OptionSet options;
		try {
			options = _parser.parse(args);
			// _maudeFile = options.valueOf(maudefile).getCanonicalPath();
			_maudeFile = options.valueOf(maudefile);
			_port = options.valueOf(port);
			_append = options.valueOf(append);
			_outputFile = options.valueOf(outputFile);
		} catch (OptionException e) {
			usageError();
		}
		
		
		FileHandler fh = new FileHandler("krunner.log", _append);
		fh.setFormatter(new SimpleFormatter());
		_logger = java.util.logging.Logger.getLogger("KRunner");
		_logger.addHandler(fh);
		_logger.setUseParentHandlers(false);
		
		// OptionSpec<File> infile = parser.accepts( "infile" ).withRequiredArg().ofType( File.class );
		// List<String> synonyms = asList( "message", "blurb", "greeting" );
        // parser.acceptsAll( synonyms ).withRequiredArg();
		// List<String> nonOptionArgs = options.nonOptionArguments();
		// if (nonOptionArgs.size() != 1) {
			// System.out.println("Please invoke with the maude file you want to execute as an argument.");
			// parser.printHelpOn(System.out);
			// System.out.println("");
			// System.exit(1);
		// }
		// String filename = nonOptionArgs.get(0);

        // OptionSpec<File> outdir =
            // parser.accepts( "outdir" ).withRequiredArg().ofType( File.class ).defaultsTo( tempDir );
        // OptionSpec<Integer> bufferSize =
            // parser.accepts( "buffer-size" ).withOptionalArg().ofType( Integer.class ).defaultsTo( 4096 );
        // OptionSpec<Level> level =
            // parser.accepts( "level" ).withOptionalArg().ofType( Level.class ).defaultsTo( INFO );
        // OptionSpec<Integer> count =
            // parser.accepts( "count" ).withOptionalArg().ofType( Integer.class ).defaultsTo( 10 );
	}
	
	Thread startServer() {
		_logger.info("Trying to start server on port " + _port);
		MainServer server = new MainServer(_port);
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
		
		Thread maude = new MaudeTask(_maudeCommand, _maudeFile, _outputFile, _logger);
		maude.start();
		_logger.info("Maude started");
		
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

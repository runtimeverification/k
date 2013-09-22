package org.kframework.krun;

import org.kframework.kil.loader.Context;
import org.kframework.krun.tasks.MaudeTask;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.ProgramLoader;
import org.kframework.utils.ThreadedStreamCapturer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings.ParserType;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

// instantiate processes
public class RunProcess {

	private String stdout = null;
	private String err = null;
	private int exitCode;

	public void execute(Map<String, String> environment,String... commands) {

		ThreadedStreamCapturer inputStreamHandler, errorStreamHandler;

		try {
			if (commands.length <= 0) {
				Error.report("Need command options to run");
			}

			// create process
			ProcessBuilder pb = new ProcessBuilder(commands);
			Map<String, String> realEnvironment = pb.environment();
			realEnvironment.putAll(environment);

			// set execution directory to current user dir
			pb.directory(new File(K.userdir));

			// start process
			Process process = pb.start();

			InputStream inputStream = process.getInputStream();
			InputStream errorStream = process.getErrorStream();
			// these need to run as java threads to get the standard output and error from the command.
			inputStreamHandler = new ThreadedStreamCapturer(inputStream);
			errorStreamHandler = new ThreadedStreamCapturer(errorStream);

			inputStreamHandler.start();
			errorStreamHandler.start();

			// wait for process to finish
			process.waitFor();
			setExitCode(process.exitValue());

			synchronized (inputStreamHandler) {
				if (inputStreamHandler.isAlive())
					inputStreamHandler.wait();
			}
			synchronized (errorStreamHandler) {
				if (errorStreamHandler.isAlive())
					errorStreamHandler.wait();
			}

			String s1 = inputStreamHandler.getContent().toString();
			if (!s1.equals("")) {
				this.setStdout(s1);
			}

			String s2 = errorStreamHandler.getContent().toString();
			// if some errors occurred (if something was written on the stderr stream)
			if (!s2.equals("")) {
				this.setErr(s2);
			}

		} catch (IOException e) {
			// e.printStackTrace();
			Error.report("Error while running process:" + e.getMessage());
		} catch (InterruptedException e) {
			// e.printStackTrace();
			Error.report("Error while running process:" + e.getMessage());
		}

	}

	public Term runParserOrDie(String parser, String pgm, boolean isPgm, String startSymbol, Context context) {
		try {
			return runParser(parser, pgm, isPgm, startSymbol, context);
		} catch (TransformerException e) {
			e.report();
			return null;
		}
	}

	/*
	 * run the process denoted by the parser ("kast" or an external parser specified with --parser option) and return the AST obtained by parser
	 */
	public Term runParser(String parser, String value, boolean isNotFile, String startSymbol, Context context) throws TransformerException {
		String KAST = new String();
		String parserPath = new String();

		if (startSymbol == null) {
			startSymbol = context.startSymbolPgm;
		}		
		String content = value;
		
		if ("kast".equals(parser)) {
            if (!isNotFile) {
		    	content = FileUtil.getFileContent(value);
		    }
			return ProgramLoader.processPgm(content, value, K.definition, startSymbol, context, ParserType.PROGRAM);
        } else if ("kast -e".equals(parser)) {
            return ProgramLoader.processPgm(value, value, K.definition, startSymbol, context, ParserType.PROGRAM);
        } else if ("kast -groundParser".equals(parser)) {
            if (!isNotFile) {
		    	content = FileUtil.getFileContent(value);
		    }
            return ProgramLoader.processPgm(content, value, K.definition, startSymbol, context, ParserType.GROUND);
        } else if ("kast -groundParser -e".equals(parser)) {
            return ProgramLoader.processPgm(value, value, K.definition, startSymbol, context, ParserType.GROUND);
        } else if ("kast -ruleParser".equals(parser)) {
            if (!isNotFile) {
		    	content = FileUtil.getFileContent(value);
		    }
            return ProgramLoader.processPgm(content, value, K.definition, startSymbol, context, ParserType.RULES);
		} else {
			List<String> tokens = new ArrayList<String>(Arrays.asList(parser.split(" ")));
			tokens.add(value);
			Map<String, String> environment = new HashMap<String, String>();
			environment.put("KRUN_SORT", startSymbol);
			environment.put("KRUN_COMPILED_DEF", context.kompiled.getAbsolutePath());
			if (isNotFile) {
				environment.put("KRUN_IS_NOT_FILE", "true");
			}
			this.execute(environment, tokens.toArray(new String[0]));
		}

		// if (parser.equals("kast")) {
		// if (this.getErr() != null) {
		// System.out.println("Warning: kast reported errors or warnings:\n" + this.getErr());
		// }
		// if (this.getExitCode() != 0) {
		// System.out.println("Kast reported:\n" + this.getStdout());
		// System.out.println("Fatal: kast returned a non-zero exit code: " + this.getExitCode());
		// Error.report("\nAttempted command:\n" + "kast --definition=" + definition + " " + pgm);
		// }
		// } else
		{
			if (this.getExitCode() != 0) {
				throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Parser returned a non-zero exit code: " + this.getExitCode() + "\nStdout:\n" + this.getStdout() + "\nStderr:\n" + this.getErr()));
			}
		}

		if (this.getStdout() != null) {
			KAST = this.getStdout();
		}
		return new BackendTerm("", KAST); //hopefully sort information will get filled in later if we need it, e.g. by SubstitutionFilter
	}

	// run the Maude process by specifying the command to execute, the output file and the error file
	public int runMaude(String command, String outputFileName, String errorFileName) {
		MaudeTask maude = new MaudeTask(command, outputFileName, errorFileName);
		maude.start();
		try {
			maude.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		if (maude.returnValue != 0) {
			System.out.println("Error " + maude.returnValue + " when executing Maude.");
			System.exit(1);
		}
		return maude.returnValue;
	}

	public void checkMaudeForErrors(File errFile, String lang, Context context) {
		if (errFile.exists()) {
			String content = FileUtil.getFileContent(K.maude_err);
			if (!content.equals("")) {
				printError(content, lang, context);
			}
		}
	}

	// check if the execution of Maude process produced some errors
	public void printError(String content, String lang, Context context) {
		try {
			if (content.contains("GLIBC")) {
				System.out.println("\nError: A known bug in the current version of the Maude rewrite engine\n" + "prohibits running K with I/O on certain architectures.\n"
						+ "If non I/O programs and definitions work but I/O ones fail, \n" + "please let us know and we'll try helping you fix it.\n");
				return;

			}
			System.out.println("Krun was executed with the following arguments:" + K.lineSeparator + "syntax_module=" + K.syntax_module
					+ K.lineSeparator + "main_module=" + K.main_module + K.lineSeparator + "compiled_def=" + K.compiled_def + K.lineSeparator);
			String compiledDefName = context.kompiled.getName();
			int index = compiledDefName.indexOf("-kompiled");
			compiledDefName = compiledDefName.substring(0, index);
			if (lang != null && !lang.equals(compiledDefName)) {
				Error.silentReport("Compiled definition file name (" + compiledDefName + ") and the extension of the program (" + lang + ") aren't the same. "
						+ "Maybe you should use --syntax-module or --main-module options of krun");
			}

			// Error.externalReport("Fatal: Maude produced warnings or errors:\n" + content);
			/*
			 * String fileName = K.krunDir + K.fileSeparator + new File(K.maude_err).getName(); Error.silentReport("Maude produced warnings or errors. See in " + fileName + " file");
			 */

			// get the absolute path on disk for the maude_err file disregard the rename of krun temp dir took place or not
			String fileName = new File(K.maude_err).getName();
			String fullPath = new File(K.kdir + K.fileSeparator + "krun" + K.fileSeparator + fileName).getCanonicalPath();
			Error.silentReport("Maude produced warnings or errors.\n" + content);
		} catch (IOException e) {
			Error.report("Error in checkMaudeForErrors method:" + e.getMessage());
		}
	}

	public String getStdout() {
		return stdout;
	}

	public void setStdout(String stdout) {
		this.stdout = stdout;
	}

	public String getErr() {
		return err;
	}

	public void setErr(String err) {
		this.err = err;
	}

	public void setExitCode(int exitCode) {
		this.exitCode = exitCode;
	}

	public int getExitCode() {
		return exitCode;
	}

}

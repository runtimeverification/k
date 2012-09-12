package ro.uaic.info.fmse.krun;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;

import ro.uaic.info.fmse.krun.tasks.MaudeTask;

// instantiate processes
public class RunProcess {

	private String stdout = null;
	private String err = null;
	private int exitCode;

	public void execute(String... commands) {

		ThreadedStreamHandler inputStreamHandler, errorStreamHandler;
		
		try {
			if (commands.length <= 0) {
				Error.report("Need command options to run");
			}

			// create process
			ProcessBuilder pb = new ProcessBuilder(commands);

			// set execution directory to current user dir
			pb.directory(new File(K.userdir));

			// start process
			Process process = pb.start();

			InputStream inputStream = process.getInputStream();
			InputStream errorStream = process.getErrorStream();
			// these need to run as java threads to get the standard output and error from the command.
			inputStreamHandler = new ThreadedStreamHandler(inputStream);
			errorStreamHandler = new ThreadedStreamHandler(errorStream);

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
			//e.printStackTrace();
			Error.report("Error while running process:" + e.getMessage());
		} catch (InterruptedException e) {
			//e.printStackTrace();
			Error.report("Error while running process:" + e.getMessage());
		}

	}
	/*
	 * run the process denoted by the parser ("kast" or an external parser specified with --parser option) 
	 * and return the AST obtained by parser
	 */
	public String runParser(String k3jar, String parser, String definition, String pgm, boolean isPgm) {
		String KAST = new String();
		String parserPath = new String(); 
		
		//the argument is a formula and we should write it in a file before passing it to the parser
		if (!isPgm) {
			FileUtil.createFile(K.kast_in, pgm);
			pgm = K.kast_in;
		}
		if ("kast".equals(parser)) {
			// rp.execute(new String[] { K.kast, "--definition=" + K.k_definition, "--main-module=" + K.main_module, "--syntax-module=" + K.syntax_module, "-pgm=" + K.pgm });
			// rp.execute(new String[] { K.kast, "--definition=" + K.k_definition, "--lang=" + K.main_module, "--syntax-module=" + K.syntax_module, K.pgm });
			this.execute(new String[] { "java", "-ss8m", "-Xms64m", "-Xmx1G", "-jar", k3jar, "-kast", "--definition", definition, pgm });
		} else {
			try {
				parserPath = new File(parser).getCanonicalPath();
			} catch (IOException e) {
				e.printStackTrace();
			}
			String parserName = new File(parserPath).getName();
			System.out.println("The external parser to be used is:" + parserName);
			if ("kast".equals(parserName)) {
				this.execute(new String[] { "java", "-ss8m", "-Xms64m", "-Xmx1G", "-jar", k3jar, "-kast", pgm });
			}
			else {
				String cmd = parser + " " + pgm;
				String[] tokens = cmd.split(" ");
				this.execute(tokens);
			}
		}
		
	    if (parser.equals("kast")) {
		  if (this.getErr() != null) {
			 System.out.println("Warning: kast reported errors or warnings:\n" + this.getErr());
		  }
		  if (this.getExitCode() != 0) {
			 System.out.println("Kast reported:\n" + this.getStdout());
			 System.out.println("Fatal: kast returned a non-zero exit code: " + this.getExitCode());
			 Error.report("\nAttempted command:\n" + "kast --definition=" + definition + " " + pgm);
		  }
	    } else {
	    	if (this.getErr() != null) {
	    		System.out.println("Warning: parser reported errors or warnings:\n" + this.getErr());
			}
	    	if (this.getExitCode() != 0) {
				 System.out.println("Parser reported:\n" + this.getStdout());
				 System.out.println("Fatal: parser returned a non-zero exit code: " + this.getExitCode());
				 Error.report("\nAttempted command:\n" + parser + " " + pgm);
			}
	    }
		
		if (this.getStdout() != null) {
			KAST = this.getStdout();
		}
		return KAST;
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
		return maude.returnValue;
	}
	
	public void checkMaudeForErrors(File errFile, String lang) {
		try {
			if (errFile.exists()) {
				String content = FileUtil.getFileContent(K.maude_err);
				if (content.length() > 0) {
					System.out.println("Krun was executed with the following arguments:" + K.lineSeparator + 
					"k_definition=" + K.k_definition + K.lineSeparator + "syntax_module=" + K.syntax_module + K.lineSeparator + 
					"main_module=" + K.main_module + K.lineSeparator + "compiled_def=" + K.compiled_def+ K.lineSeparator);
					 String compiledDefName = FileUtil.getFilename(K.compiled_def, ".", K.fileSeparator);
					 int index = compiledDefName.indexOf("-compiled");
					 compiledDefName = compiledDefName.substring(0, index);
					 if (!lang.equals(compiledDefName)) {
						 Error.silentReport("Compiled definition file name (" + compiledDefName + ") and the extension of the program (" + lang + ") aren't the same. " +
						 		"Maybe you should use --syntax-module or --main-module options of krun");
					 }
					
					//Error.externalReport("Fatal: Maude produced warnings or errors:\n" + content);
					/*String fileName = K.krunDir + K.fileSeparator + new File(K.maude_err).getName();
					Error.silentReport("Maude produced warnings or errors. See in " + fileName + " file");*/
					
					//get the absolute path on disk for the maude_err file disregard the rename of krun temp dir took place or not
					String fileName = new File(K.maude_err).getName();
					ArrayList<File> files = FileUtil.searchFiles(K.kdir, "txt", true);
					for (File file : files) {
						if (file.getName().equals(fileName)) {
							String fullPath = file.getCanonicalPath();
							Error.silentReport("Maude produced warnings or errors. See in " + fullPath + " file");
						}
					}
				}
			}
		}
		catch (IOException e) {
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

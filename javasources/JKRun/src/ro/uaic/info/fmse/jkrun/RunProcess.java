package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;

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
		
		//the argument is a formula and we should write in a file before passing it to kast
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
				parser = new File(parser).getCanonicalPath();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			System.out.println("The external parser to be used is:" + parser);
			String parserName = new File(parser).getName();
			if ("kast".equals(parserName)) {
				this.execute(new String[] { "java", "-ss8m", "-Xms64m", "-Xmx1G", "-jar", k3jar, "-kast", pgm });
			}
			else {
				this.execute(new String[] { parser, pgm });
			}
		}
		
	    if (parser.equals("kast")) {
		  if (this.getErr() != null) {
			Error.externalReport("Warning: kast reported errors or warnings:\n" + this.getErr());
		  }
		  if (this.getExitCode() != 0) {
			 System.out.println("Kast reported:\n" + this.getStdout());
			 System.out.println("Fatal: kast returned a non-zero exit code: " + this.getExitCode());
			 Error.report("\nAttempted command:\n" + "kast --definition=" + definition + " " + pgm);
		  }
	    } else {
	    	if (this.getErr() != null) {
	    		Error.externalReport("Warning: parser reported errors or warnings:\n" + this.getErr());
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

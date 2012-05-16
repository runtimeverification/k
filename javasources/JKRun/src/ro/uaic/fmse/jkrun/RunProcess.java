package ro.uaic.fmse.jkrun;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

// instantiate processes
public class RunProcess {

	private String stdout = null;
	private String err = null;

	public String getStdout() {
		return stdout;
	}

	public void setStdout(String stdout) {
		this.stdout = stdout;
	}

	// catch error
	public String getErr() {
		return err;
	}

	public void setErr(String err) {
		this.err = err;
	}

	public void execute(String... commands) {

		ThreadedStreamHandler inputStreamHandler, errorStreamHandler;
		try {
			if (commands.length <= 0) {
				System.out.println("Need command options to run");
				System.exit(-1);
			}

			// create process
			ProcessBuilder pb = new ProcessBuilder(commands);

			// set execution directory to current user dir
			pb.directory(new File(K.userdir));

			// set environment variables for this process
			/*Map<String, String> environment = pb.environment();
			environment.put("PATH", System.getenv("PATH"));
			environment.put("K_BASE", System.getenv("K_BASE"));*/
			// environment.put("PERL", K.perl);

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

			synchronized (inputStreamHandler) {
				if (inputStreamHandler.isAlive())
					inputStreamHandler.wait();
			}
			synchronized (errorStreamHandler) {
				if (errorStreamHandler.isAlive())
					errorStreamHandler.wait();
			}

			/*
			 * inputStreamHandler.interrupt(); errorStreamHandler.interrupt(); inputStreamHandler.join(); errorStreamHandler.join(); */

			String s1 = inputStreamHandler.getContent().toString();
			if (!s1.equals("")) {
				// System.out.println("Output is:" + s1);
				this.setStdout(s1);
			}

			String s2 = errorStreamHandler.getContent().toString();

			// if some errors occurred (if something was written on the stderr stream)
			if (!s2.equals("")) {
				System.out.println("RunProcess: Some errors occurred.." + s2);
				this.setErr(s2);
				System.exit(1);
			}

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

}

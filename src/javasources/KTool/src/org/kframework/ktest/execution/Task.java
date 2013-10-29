package org.kframework.ktest.execution;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.regex.Pattern;

import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.apache.commons.io.IOUtils;
import org.kframework.ktest.Configuration;

public class Task extends Thread {

	// standard
	private String stderr, stdout;
	private String[] arguments;
	private int exit;
	private String stdin;
	private long elapsed;
	private File homeDir;

	public Task(String[] arguments, String stdin, File homeDir) {
		super();
		this.arguments = arguments;
		this.stdin = stdin;
		this.stderr = "";
		this.stdout = "";
		this.exit = 0;
		this.homeDir = homeDir;
	}

	@Override
	public void run() {
		try {
			ProcessBuilder pb = new ProcessBuilder(arguments);
			pb.directory(homeDir);
			String message = "";
			if (Configuration.VERBOSE) {
				message = "Done with [" + pb.command().get(1);
//				for (String cmd : pb.command())
//					message += cmd + " ";
			}
			elapsed = System.currentTimeMillis();
			Process p = pb.start();
			//System.out.println("Start process...");

			try {
				// asynchronous output reader
				final ExecutorService service = Executors.newFixedThreadPool(2);
				final Future<String> outputGobbler = service.submit(new StreamGobbler(p.getInputStream()));
				final Future<String> errorGobbler  = service.submit(new StreamGobbler(p.getErrorStream()));

				// send input
				if (stdin != null) {
					p.getOutputStream().write(stdin.getBytes());
					p.getOutputStream().flush();
					p.getOutputStream().close();
				}

				// wait output reader
				try {
					stdout = outputGobbler.get();
					stderr = errorGobbler.get();
				} catch(final InterruptedException ie) {
					ie.printStackTrace();
				} catch(final ExecutionException ee) {
					ee.printStackTrace();
				}

				// exit value
				exit = p.waitFor();

				try {
					service.shutdownNow();
					if (!service.awaitTermination(Configuration.KOMPILE_ALL_TIMEOUT, TimeUnit.SECONDS)) {
						//System.out.println("Still waiting...");
						System.exit(1);
					}
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				//System.out.println("Finished process");

			} catch (InterruptedException e) {
				exit = Integer.MAX_VALUE;
				p.destroy();
			}

			// time
			elapsed = (System.currentTimeMillis() - elapsed);

			/*
			// clean
			p.getInputStream().close();
			p.getErrorStream().close();
			p.destroy();
			*/
			if (Configuration.VERBOSE) {
				System.out.println(message + "] (time: " + elapsed + " ms)");
			}

		} catch (IOException io) {
			exit = Integer.MAX_VALUE;
		}
	}

	public String getStderr() {
		if (stderr == null)
			return "";
		return stderr;
	}

	public String getStdout() {
		if (stdout == null)
			return "";
		return stdout;
	}

	public int getExit() {
		return exit;
	}

	public long getElapsed() {
		return elapsed / 1000;
	}

    public String getCommand() {
        String cmd = "";
        for (String s : arguments) {
            if (Pattern.compile("\\s").matcher(s).find()) {
                cmd += "\"" + s + "\" ";
            } else {
                cmd += s + " ";
            }
        }
        return cmd;
    }
}

class StreamGobbler implements Callable<String> {
	InputStream is;

	StreamGobbler(InputStream is) {
		this.is = is;
	}

	public String call() {
        try {
            return IOUtils.toString(is);
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }
}

// vim: noexpandtab

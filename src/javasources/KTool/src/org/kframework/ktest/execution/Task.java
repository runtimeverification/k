package org.kframework.ktest.execution;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

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

			// send input
			if (stdin != null) {
				p.getOutputStream().write(stdin.getBytes());
				p.getOutputStream().flush();
				p.getOutputStream().close();
			}
			// get output
			stdout = readString(p.getInputStream());

			// get error
			stderr = readString(p.getErrorStream());

			// exit value
			exit = p.waitFor();

			// time
			elapsed = (System.currentTimeMillis() - elapsed);

			// clean
			p.getInputStream().close();
			p.getErrorStream().close();
			p.destroy();
			if (Configuration.VERBOSE) {
				System.out.println(message + "] (time: " + elapsed + " ms)");
			}

		} catch (IOException io) {
			exit = Integer.MAX_VALUE;
		} catch (InterruptedException e) {
			exit = Integer.MAX_VALUE;
		}
	}

	public static String readString(InputStream is) {
		try {
			BufferedReader br = new BufferedReader(new InputStreamReader(is));

			StringBuilder sb = new StringBuilder();

			String line;
			while ((line = br.readLine()) != null) {
				sb.append(line);
				sb.append(System.getProperty("line.separator"));
			}

			br.close();
			return sb.toString();
		} catch (IOException e) {
			e.printStackTrace();
		}

		return "";
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
}

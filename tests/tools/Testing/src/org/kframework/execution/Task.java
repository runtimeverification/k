package org.kframework.execution;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class Task extends Thread {

	// standard
	private String stderr, stdout;
	private String[] arguments;
	private int exit;
	private String stdin;
	private long elapsed;

	public Task(String[] arguments, String stdin) {
		super();
		this.arguments = arguments;
		this.stdin = stdin;
		this.stderr = "";
		this.stdout = "";
		this.exit = 0;
	}

	@Override
	public void run() {
		try {
			ProcessBuilder pb = new ProcessBuilder(arguments);

//			String message = "Executing ";
//			for(String cmd : pb.command())
//				message += cmd.replaceAll(Configuration.getHome(), "") + " ";
			elapsed = System.currentTimeMillis();
			Process p = pb.start();

			// send input
			if (stdin != null)
			{
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
			elapsed = System.currentTimeMillis() - elapsed;

			// clean
			p.getInputStream().close();
			p.getErrorStream().close();
			p.destroy();
//			System.out.println(message + " ... Done.");

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
		return stderr;
	}

	public String getStdout() {
		return stdout;
	}

	public int getExit() {
		return exit;
	}

	public long getElapsed() {
		return elapsed;
	}
}

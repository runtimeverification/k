import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

public class Executor extends Thread {

	private String[] commands;
	private String dir;
	private String output = "", error = "";
	private int exitValue;

	public Executor(String[] commands, String dir) {
		super();
		this.commands = commands;
		this.dir = dir;
	}

	@Override
	public void run() {
		try {
			ProcessBuilder pb = new ProcessBuilder(commands);
			pb.directory(new File(dir));
			Process p = pb.start();

			exitValue = p.waitFor();
			BufferedReader br = new BufferedReader(new InputStreamReader(
					p.getInputStream()));
			String line;
			while ((line = br.readLine()) != null) {
				output += line + "\n";
			}

			br = new BufferedReader(new InputStreamReader(p.getErrorStream()));
			line = "";
			while ((line = br.readLine()) != null) {
				error += line + "\n";
			}

		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}

	public String[] getCommands() {
		return commands;
	}

	public String getOutput() {
		return output;
	}

	public String getError() {
		return error;
	}

	public int getExitValue() {
		return exitValue;
	}
}


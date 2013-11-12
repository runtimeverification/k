package org.kframework.ktest.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.ktest.Configuration;
import org.kframework.ktest.execution.Task;

public class Program implements Comparable<Program> {
	final String programPath;
	final Map<String, String> krunOptions;
	private final Test test;
	private final String input;
    private final String output;
    private final String error;
    private boolean hasInput = false;
    private boolean hasOutput = false;

	public Program(String name, Map<String, String> map, Test test,
			String input, String output, String error) {
		this.programPath = name;
		this.krunOptions = map;
		this.test = test;
		this.input = input;
		this.output = output;
		this.error = error;
        hasInput = this.input != null;
        hasOutput = this.output != null;
	}

	@Override
	public String toString() {
		return programPath;
	}

	public Task getTask(File homeDir) {
		ArrayList<String> command = new ArrayList<String>();
		command.add(Configuration.getKrun());
		command.add(programPath);
		command.add("--directory");
		command.add(test.getDirectory());
		for (Entry<String, String> entry : krunOptions.entrySet()) {
			command.add(entry.getKey());
			command.add(entry.getValue());
		}

		String[] arguments = new String[command.size()];
		int i = 0;
		for (String cmd : command) {
			arguments[i] = cmd;
			i++;
		}

		return new Task(arguments, input, homeDir);
	}

	public boolean success(Task task) {
		if (error != null && !eq(task.getStderr(), error))
			return false;
		
		if (output != null && !eq(task.getStdout(), output))
			return false;

		if (error == null && task.getExit() != 0)
			return false;

		return true;
	}
	private boolean eq(String s1, String s2) {
		if (Configuration.IGNORE_WHITE_SPACES) {
			s1 = s1.replaceAll("\\r|\\s|\\n","");
			s2 = s2.replaceAll("\\r|\\s|\\n","");
			s1 = s1.replaceAll("\u001B\\[[;\\d]*m", "");
			s2 = s2.replaceAll("\u001B\\[[;\\d]*m", "");
		} else {
			s1 = s1.replaceAll("\\r","");
			s2 = s2.replaceAll("\\r","");
		}
		if (Configuration.IGNORE_BALANCED) {
			s1 = removeAllBalanced(s1);
			s2 = removeAllBalanced(s2);
		}
		return s1.trim().equals(s2.trim());
	}
	private static String removeAllBalanced(String s1) {
		String s2 = s1.replaceAll("\\((.*?)\\)", "$1")
					  .replaceAll("\\{(.*?)\\}", "$1")
					  .replaceAll("\\[(.*?)\\]", "$1");
		if (s1.equals(s2)) {
			return s1;
		} else {
			return removeAllBalanced(s2);
		}
	}

	public String successful(Task task) {
		return success(task) ? "success" : "failed";
	}

	public void reportTest(Task value) {
		test.report.appendChild(test.createReportElement(
				new File(programPath).getName(), successful(value),
				value.getElapsed() + "", value.getStdout(), value.getStderr(),
				value, output, !success(value)));
        if (Configuration.REPORT)
		    test.save();
	}

	public String getProgramPath() {
		return programPath;
	}

	@Override
	public int compareTo(Program o) {
		int d;
		if (o == this) return 0;
		d = programPath.compareTo(o.programPath);
		if (d != 0) return d;
		d = test.compareTo(o.test);
		return d;
	}

    public boolean hasInput() {
        return hasInput;
    }

    public boolean hasOutput() {
        return hasOutput;
    }
}

// vim: noexpandtab

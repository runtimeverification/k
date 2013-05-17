package org.kframework.tests;

import org.kframework.execution.Task;
import org.kframework.main.Configuration;

import java.io.File;
import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;

public class Program implements Comparable<Program> {
	String programPath;
	Map<String, String> krunOptions;
	Test test;
	String input, output, error;

	public Program(String name, Map<String, String> map, Test test,
			String input, String output, String error) {
		this.programPath = name;
		this.krunOptions = map;
		this.test = test;
		this.input = input;
		this.output = output;
		this.error = error;
	}

	@Override
	public String toString() {
		return programPath;
	}

	public Task getTask(File homeDir) {
		ArrayList<String> command = new ArrayList<String>();
		command.add(Configuration.getKrun());
		command.add(programPath);
		command.add("--k-definition");
		command.add(test.getLanguage());
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
		if (!task.getStderr().equals(error) && error != null)
			return false;
		
		if (!task.getStdout().equals(output) && output != null)
			return false;

		if (error == null && task.getExit() != 0)
			return false;
		
		return true;
	}

	public String successful(Task task) {
		return success(task) ? "success" : "failed";
	}

	public void reportTest(Task value) {
		test.report.appendChild(test.createReportElement(
				new File(programPath).getName(), successful(value),
				value.getElapsed() + "", value.getStdout(), value.getStderr(),
				value, output, !success(value)));
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
}

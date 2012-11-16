package org.kframework.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.execution.Task;
import org.kframework.main.Configuration;

public class Program {
	String absolutePath;
	Map<String, String> krunOptions;
	Test test;
	String input, output;

	public Program(String name, Map<String, String> map, Test test,
			String input, String output) {
		this.absolutePath = name;
		this.krunOptions = map;
		this.test = test;
		this.input = input;
		this.output = output;
	}

	@Override
	public String toString() {
		return absolutePath;// + "\nIn: " + input + "\nOut: " + output + "\n";
	}

	public Task getTask() {
		ArrayList<String> command = new ArrayList<String>();
		command.add(Configuration.getKrun());
		command.add(absolutePath);
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

		return new Task(arguments, input);
	}

	public boolean success(Task task) {
		if (task.getExit() != 0)
			return false;

		if (!task.getStderr().equals(""))
			return false;

		if (!task.getStdout().equals(output) && output != null)
			return false;

		return true;
	}

	public String successful(Task task) {
		String message = success(task) ? "success" : "failed";
		if (!task.getStdout().equals(""))
			if (message.equals("success"))
				message = "unstable";

		return message;
	}

	public void reportTest(Task value) {
		test.report.appendChild(test.createReportElement(
				new File(absolutePath).getName(), successful(value),
				value.getElapsed() + "", value.getStdout(), value.getStderr(),
				value, output, !success(value)));
		test.save();
	}

	public String getAbsolutePath() {
		return absolutePath;
	}
}

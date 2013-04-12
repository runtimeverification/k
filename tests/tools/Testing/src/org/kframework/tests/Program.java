package org.kframework.tests;

import org.kframework.execution.Task;
import org.kframework.main.Configuration;

import java.io.File;
import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;

public class Program {
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

	public Task getTask() {
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

		return new Task(arguments, input);
	}

	public boolean success(Task task) {
//		System.out.println(this.programPath);
//		System.out.println("e>>>" + error + "<<<");
//		System.out.println("e>>>" + task.getStderr() + "<<<");
//		if(error !=null)
//		System.out.println("e>>>" + task.getStderr().equals(error) + "<<<");
		if (!task.getStderr().equals(error) && error != null)
			return false;
		
//		System.out.println("o>>>" + output + "<<<");
//		System.out.println("o>>>" + task.getStdout() + "<<<");
		if (!task.getStdout().equals(output) && output != null)
			return false;

//		System.out.println("x>>>" + task.getExit() + "<<<");
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
}

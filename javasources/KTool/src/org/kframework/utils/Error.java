package org.kframework.utils;

import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;

import java.util.Comparator;

public class Error {

	public static void report(String message) {
		System.out.println("Error: " + message);
		System.exit(1);
	}

	public static void externalReport(String message) {
		System.out.println(message);
		System.exit(1);
	}

	public static void silentReport(String localizedMessage) {
		System.out.println("Warning: " + localizedMessage);
	}

	public static void helpExit(HelpFormatter help, Options options) {
		helpExit(help, "help", options);
	}

	public static void helpExit(HelpFormatter help, String cmdLineSyntax, Options options) {
		System.out.println("\n");
		help.printHelp(cmdLineSyntax, "\nCompiles the K definitions given as arguments.\n\n", options, "\n", true);
		System.out.println("\n");
		System.exit(1);
	}

	public static void helpMsg(String usage, String header, String footer, Options options, Comparator comparator) {
		HelpFormatter helpFormatter = new HelpFormatter();
		helpFormatter.setOptionComparator(comparator);
		helpFormatter.setWidth(79);
		helpFormatter.printHelp(usage, header, options, footer);
		System.out.println();
		//System.exit(1);
	}
}

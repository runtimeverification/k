package ro.uaic.fmse.jkrun;

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

	public static void usageError(String message) {
		System.out.println("jkrun: " + message);
		System.out.println("Type 'jkrun --help' for more information.");
		System.exit(1);
	}
}

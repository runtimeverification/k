package ro.uaic.info.fmse.krun;

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
		System.out.println("krun: " + message);
		System.out.println("Type 'krun --help' for more information.");
		System.exit(1);
	}
}

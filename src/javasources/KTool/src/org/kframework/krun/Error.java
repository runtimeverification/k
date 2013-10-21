package org.kframework.krun;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

// helper class for handling error messages
public class Error {

	public static void report(String message) {
		GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message));
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

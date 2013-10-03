package org.kframework.main;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Arrays;

import org.kframework.kagreg.KagregFrontEnd;
import org.kframework.kcheck.KCheckFrontEnd;
import org.kframework.ktest.KTest;
import org.kframework.utils.Error;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class Main {

	/**
	 * Sets the {@code java.library.path} system property to include the native libraries
	 * directory for this platform.
	 */
	private static void setJavaLibraryPath() {
        String javaLibraryPath = KPaths.getJavaLibraryPath();

		System.setProperty("java.library.path", javaLibraryPath);

		/* force java to reset the path (dirty hack) */
		try {
			Field fieldSysPath = ClassLoader.class.getDeclaredField("sys_paths");
			fieldSysPath.setAccessible(true);
			fieldSysPath.set(null, null);
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		} catch (NoSuchFieldException e) {
			e.printStackTrace();
		}
	}

	/**
	 * @param args
	 *            - the running arguments for the K3 tool. First argument must be one of the following: kompile|kast|krun.
	 * @throws Exception when loadDefinition fails
	 * @throws IOException when loadDefinition fails 
	 */
	public static void main(String[] args) throws Exception {
		setJavaLibraryPath();

		if (args.length >= 1) {
            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
			if (args[0].equals("-kompile")) {
				org.kframework.kompile.KompileFrontEnd.kompile(args2);
			} else if (args[0].equals("-kagreg")) {
				KagregFrontEnd.kagreg(args2);
			} else if (args[0].equals("-kcheck")) {
				KCheckFrontEnd.kcheck(args2);
			} else if (args[0].equals("-ktest")) {
				KTest.test(args2);
			} else if (args[0].equals("-kast")) {
				org.kframework.kast.KastFrontEnd.kast(args2);
			} else if (args[0].equals("-krun")) {
				org.kframework.krun.Main.execute_Krun(args2);
			} else if (args[0].equals("-kpp")) {
				org.kframework.main.Kpp.codeClean(args2);
			} else if (args[0].equals("-ioserver")) {
				try {
					org.kframework.krun.ioserver.main.MainServer.main(args2);
				} catch (Exception e) {
					Error.report("IO server threw exception");
				}
			} else if (args[0].equals("-kpretty")) {
				org.kframework.main.KPretty.main(args2);
			} else {
				Error.report("The first argument of K3 not recognized. Try -kompile, -kast, -krun or -kpp.");
			}
		} else
			Error.report("There must be a first argument to K3: try -kompile, -kast, -krun or -kpp.");
	}
}

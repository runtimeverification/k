package org.kframework.main;

import java.awt.GraphicsEnvironment;
import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Arrays;

import org.kframework.utils.Error;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class Main {

	/**
	 * Sets the {@code java.library.path} system property to include the native libraries
	 * directory containing extra Jar files distributed with K for this platform.
	 */
	private static void setJavaLibraryPath() {
		System.setProperty("java.library.path", KPaths.getJavaLibraryPath());

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
        Stopwatch.init();
		setJavaLibraryPath();

		if (args.length >= 1) {
            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
			if (args[0].equals("-kompile")) {
				org.kframework.kompile.KompileFrontEnd.main(args2);
			} else if (args[0].equals("-kagreg")) {
				org.kframework.kagreg.KagregFrontEnd.kagreg(args2);
			} else if (args[0].equals("-kcheck")) {
				org.kframework.kcheck.KCheckFrontEnd.kcheck(args2);
			} else if (args[0].equals("-ktest")) {
				org.kframework.ktest.KTest.main(args2);
			} else if (args[0].equals("-kast")) {
				org.kframework.kast.KastFrontEnd.kast(args2);
			} else if (args[0].equals("-krun")) {
			    // unable to load commandlineOptions since it loads K class 
			    // K loads Color which sets headless field in GraphicsEnvironment 
			    // and since this can be set only once we can not reset it by java.awt.headless
			    for (String s : args){
			        if(s.contains("debug-gui")){
			            System.setProperty("java.awt.headless", "false");
			            //force headless filed to be instantiated
			            java.awt.GraphicsEnvironment.isHeadless() ;
			            break;
			        }
			    }
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

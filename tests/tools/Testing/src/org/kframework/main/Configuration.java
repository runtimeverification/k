package org.kframework.main;

import java.io.File;


public class Configuration {

	public static final String FS = System.getProperty("file.separator");
	public static String kompile = getHome() + FS + "dist" + FS + "bin" + FS + "kompile";
	public static String krun = getHome() + FS + "dist" + FS + "bin" + FS + "krun";
	public static final String config = getHome() + FS + "tests" + FS + "config.xml";
	public static final long KOMPILE_ALL_TIMEOUT = 3;
	public static final String JR = "junit-reports";
	public static String k = "/var/lib/jenkins/workspace/k-framework-tests/k";

	public static String getHome() {
		if (System.getProperty("user.dir").contains("jenkins"))
			return k;
		
		return new File(System.getProperty("user.dir")).getParentFile()
				.getParentFile().getParentFile().getAbsolutePath();
	}
}

package org.kframework.main;

import java.io.File;

public class Configuration {

	public static final String FS = System.getProperty("file.separator");
	public static final long KOMPILE_ALL_TIMEOUT = 3;
	public static final String JR = "junit-reports";
	public static String k = "/var/lib/jenkins/workspace/k-framework-tests/k";
	public static String CONFIG = null; 
	
	public static String getHome() {
		if (System.getProperty("user.dir").contains("jenkins"))
			return k;

		return new File(System.getProperty("user.dir")).getAbsolutePath();
	}

	public static String getConfig() {
		if (CONFIG != null)
			return CONFIG;
		
		return getHome() + FS + "tests" + FS + "config.xml";
	}

	public static String getKompile() {
		String os = System.getProperty("os.name").toLowerCase();
		if (os.contains("win")) {
			return getHome() + FS + "dist" + FS + "bin" + FS + "kompile.bat";
		}
		return getHome() + FS + "dist" + FS + "bin" + FS + "kompile";
	}

	public static String getKrun() {
		String os = System.getProperty("os.name").toLowerCase();
		if (os.contains("win")) {
			return getHome() + FS + "dist" + FS + "bin" + FS + "krun.bat";
		}
		return getHome() + FS + "dist" + FS + "bin" + FS + "krun";
	}
}

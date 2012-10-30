package org.kframework.main;

import java.io.File;

public class Configuration {

	public static String getHomeDir() {
		return new File(System.getProperty("user.dir")).getParentFile()
				.getParentFile().getParentFile().getAbsolutePath();
	}
	
	public static final String FS = System.getProperty("file.separator");
	public static final String kompile = getHomeDir() + FS + "dist" + FS + "bin" + FS + "kompile";
	public static final String krun = getHomeDir() + FS + "dist" + FS + "bin" + FS + "krun";
	public static final String config = getHomeDir() + FS + "tests" + FS + "config.xml";
	public static final long KOMPILE_ALL_TIMEOUT = 3;
	
}

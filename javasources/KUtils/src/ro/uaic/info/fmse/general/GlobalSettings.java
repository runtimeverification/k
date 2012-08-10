package ro.uaic.info.fmse.general;

import java.io.File;

import ro.uaic.info.fmse.errorsystem.KExceptionManager;

public class GlobalSettings {
	public static boolean verbose = false;
	public static boolean noFilename = false;
	public static String startFile = "";
	public static String lib = "";
	public static boolean literate = false;
	public static String synModule = null;
	public static KExceptionManager kem = new KExceptionManager();
	public static File mainFile;
	public static String mainFileWithNoExtension;
	public static int warningslevel = 2;
	public static boolean tempDisamb = true;
	public static boolean typeWarnings = false;
}

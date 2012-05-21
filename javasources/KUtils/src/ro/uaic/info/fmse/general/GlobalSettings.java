package ro.uaic.info.fmse.general;

import ro.uaic.info.fmse.errorsystem.KExceptionManager;

public class GlobalSettings {
	public static boolean verbose = false;
	public static boolean noFilename = false;
	public static String startFile = "";
	public static String lib = ""; 
	public static String synModule = null;
	public static KExceptionManager kem = new KExceptionManager();
}

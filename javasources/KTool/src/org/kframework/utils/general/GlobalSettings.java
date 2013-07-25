package org.kframework.utils.general;

import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class GlobalSettings {
	public static boolean verbose = false;
	public static boolean noFilename = false;
	public static String startFile = "";
	public static String lib = "";
	public static String synModule = null;
	public static KExceptionManager kem = new KExceptionManager();
	public static File mainFile;
	public static String mainFileWithNoExtension;
	public static String warnings = "normal";
	public static List<String> transition = new ArrayList<String>();
	public static List<String> superheat = new ArrayList<String>();
	public static List<String> supercool = new ArrayList<String>();
	static {
		transition.add("transition");
		superheat.add("superheat");
		supercool.add("supercool");
	}
	public static boolean addTopCell = false;
	public static String style = "poster,style=bubble";
	public static boolean fastKast = false;
	
	// this is used by kast to know what parser to use fort the input string
	public static ParserType whatParser = ParserType.PROGRAM;
	public static boolean sortedCells = false;

    public static boolean isUnixOS() {
		String os = System.getProperty("os.name").toLowerCase();
		return os.contains("nix") || os.contains("nux");
	}

    public static boolean isWindowsOS() {
		return System.getProperty("os.name").toLowerCase().contains("win");
	}

    public static boolean isMacOS() {
		return System.getProperty("os.name").toLowerCase().contains("mac");
	}

    public enum ParserType {
		PROGRAM, GROUND, RULES, BINARY
	}

	public static boolean symbolicEquality = false;
	public static boolean SMT = false;
	public static boolean matchingLogic = false;
	public static boolean documentation = false;
	public static boolean xml = false;
	public static boolean NOSMT = false;
	
	public static String CHECK = null;
	public static boolean symbolic = false; // true if the --symbolic argument has been provided to kompile
}

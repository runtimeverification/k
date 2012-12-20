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
	public static boolean hiddenWarnings = false;
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
	public static boolean testFactory = false;
}

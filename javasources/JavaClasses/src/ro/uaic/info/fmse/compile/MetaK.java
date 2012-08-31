package ro.uaic.info.fmse.compile;

import java.util.Arrays;

public class MetaK {
	public static String nextIdModules[] = {
		"SUBSTITUTION",
	};
	
	public static String kModules[] = {
	    "K-CONDITION-SEARCH", 
	    "K-CONFIG",
		"K-CONTEXTS", 
	    "K-LATEX",
	    "K-OPEN-CELLS",
	    "K-POLYMORPHIC-VARIABLES",  
		"K-PROPER", 
	    "K-QUOTED-LABELS",
		"K-RESULT",
	    "K-RULES", 
		"K-SENTENCE", 
		"K-STRICNESS",
		"K-TECHNIQUE",
		"K-WHERE",  
	    "K-WRAPPERS", 
	    "K-WRAPPERS-LABELS", 
		};
	
	public static boolean isKModule(String key) {
		return (Arrays.binarySearch(kModules, key) >= 0);		
	}
	
	public static boolean isNextIdModule(String key) {
		return (Arrays.binarySearch(nextIdModules, key) >= 0);		
	}
	
	public static boolean isBuiltinModule(String key) {
		return key.startsWith("#");
	}
	
	
}

package ro.uaic.info.fmse.compile.utils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.visitors.BasicVisitor;
import ro.uaic.info.fmse.visitors.Visitable;

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

	public static Set<Variable> getVariables(Visitable node) {
		final Set<Variable> result = new HashSet<Variable>();
		node.accept(new BasicVisitor() {
			@Override
			public void visit(Variable node) {
				result.add(node);
			}
		});
		return result;
	}

}

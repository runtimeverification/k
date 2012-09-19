package org.kframework.parser.latex;

import org.kframework.parser.latex.lib.*;
import org.spoofax.interpreter.terms.*;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.StrategoExit;


public class K3LatexParser {
	private static Context context = null;

	private static void init() {
		synchronized (K3LatexParser.class) {
			if (context == null) {
				context = K3Latex.init();
			}
		}
	}

	public static String ParseKString(String kDefinition) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(java$Parse$String_0_0.instance, "a.exe", kDefinition);

			} finally {
				context.getIOAgent().closeAllFiles();
			}
			if (result == null) {
				System.err.println("rewriting failed, trace:");
				context.printStackTrace();
				context.setStandAlone(false);
				System.exit(1);
			} else {
				context.setStandAlone(false);
			}
		} catch (StrategoExit exit) {
			context.setStandAlone(false);
			System.exit(exit.getValue());
		}

		if (result.getTermType() == IStrategoTerm.STRING) {
			rez = (((IStrategoString) result).stringValue());
		} else {
			rez = result.toString();
		}
		return rez;
	}
}

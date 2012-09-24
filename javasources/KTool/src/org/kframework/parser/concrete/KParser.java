package org.kframework.parser.concrete;

import org.kframework.parser.concrete.lib.K3Str;
import org.kframework.parser.concrete.lib.import$Cells_0_0;
import org.kframework.parser.concrete.lib.import$Cons_0_0;
import org.kframework.parser.concrete.lib.import$Sbs_0_0;
import org.kframework.parser.concrete.lib.import$Tbl$Pgm_0_0;
import org.kframework.parser.concrete.lib.import$Tbl_0_0;
import org.kframework.parser.concrete.lib.init$Me_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Config_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Pgm_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Rules_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Cmd_0_0;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.StrategoExit;

public class KParser {
	private static Context context = null;

	private static void init() {
		synchronized (KParser.class) {
			if (context == null) {
				context = K3Str.init();
			}
		}
	}

	/**
	 * This is for testing only.
	 * 
	 * @return
	 */
	@Deprecated
	public static String InitMe() {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(init$Me_0_0.instance, "a.exe");
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

	public static String ImportTbl(String filePath) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(import$Tbl_0_0.instance, "a.exe", filePath);
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

	public static String ImportTblPgm(String filePath) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(import$Tbl$Pgm_0_0.instance, "a.exe", filePath);
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

	public static String ImportSbs(String filePath) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(import$Sbs_0_0.instance, "a.exe", filePath);
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

	public static String ImportCons(String filePath) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(import$Cons_0_0.instance, "a.exe", filePath);
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

	public static String ImportCells(String filePath) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(import$Cells_0_0.instance, "a.exe", filePath);
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

	public static String ParseKConfigString(String kDefinition) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(java$Parse$String$Config_0_0.instance, "a.exe", kDefinition);
			} finally {
				context.getIOAgent().closeAllFiles();
			}
			if (result == null) {
				System.err.println("Input: " + kDefinition);
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

	public static String ParseKRuleString(String kDefinition) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(java$Parse$String$Rules_0_0.instance, "a.exe", kDefinition);
			} finally {
				context.getIOAgent().closeAllFiles();
			}
			if (result == null) {
				System.out.println("Input: " + kDefinition);
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

	/**
	 * Parses a term that is subsorted to K, List, Set, Bag or Map
	 * 
	 * @param argument
	 *            The string content of the term.
	 * @return The xml representation of the parsed term, or an error in the xml format.
	 */
	public static String ParseKCmdString(String argument) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(java$Parse$String$Cmd_0_0.instance, "a.exe", argument);
			} finally {
				context.getIOAgent().closeAllFiles();
			}
			if (result == null) {
				System.out.println("Input: " + argument);
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

	public static String ParseProgramString(String program) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(java$Parse$String$Pgm_0_0.instance, "a.exe", program);
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

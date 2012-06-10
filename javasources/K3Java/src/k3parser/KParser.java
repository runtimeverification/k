package k3parser;

import org.spoofax.interpreter.terms.*;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.StrategoExit;

import ro.uaic.info.fmse.general.GlobalSettings;

import k3parser.lib.*;

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

	public static String ImportDitto(String filePath) {
		init();
		String rez = "";
		context.setStandAlone(true);
		IStrategoTerm result = null;
		try {
			try {
				result = context.invokeStrategyCLI(import$Ditto_0_0.instance, "a.exe", filePath);
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
				if (GlobalSettings.tempDisamb)
					result = context.invokeStrategyCLI(java$Parse$String$Rules_0_0.instance, "a.exe", kDefinition, "half");
				else
					result = context.invokeStrategyCLI(java$Parse$String$Rules_0_0.instance, "a.exe", kDefinition, "full");
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

// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete;

import java.io.File;
import java.util.HashSet;

import org.kframework.parser.concrete.lib.ConcreteMain;
import org.kframework.parser.concrete.lib.import$Tbl$Ground_0_0;
import org.kframework.parser.concrete.lib.import$Tbl$Pgm_0_0;
import org.kframework.parser.concrete.lib.import$Tbl_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Cmd_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Config_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Pgm_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Rules_0_0;
import org.kframework.parser.concrete.lib.java$Parse$String$Kore_0_0;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.StrategoExit;

public class KParser {
    private static Context context = null;
    private static HashSet<String> tables = new HashSet<String>();

    public static void reset() {
        context = null;
        tables = new HashSet<String>();
    }

    private static void init() {
        synchronized (KParser.class) {
            if (context == null) {
                context = ConcreteMain.init();
            }
        }
    }

    public static String ImportTblRule(File kompiled) {
        return ImportTbl(kompiled.getAbsolutePath() + "/Rule.tbl");
    }

    public synchronized static String ImportTbl(String filePath) {

        if (!tables.contains(filePath)) {
            tables.add(filePath);

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
                    throw KEMException.internalError("Stratego rewriting failed");
                } else {
                    context.setStandAlone(false);
                }
            } catch (StrategoExit exit) {
                context.setStandAlone(false);
                throw KEMException.internalError("Stratego rewriting failed", exit);
            }

            if (result.getTermType() == IStrategoTerm.STRING) {
                rez = (((IStrategoString) result).stringValue());
            } else {
                rez = result.toString();
            }
            return rez;
        }
        return null;
    }

    public synchronized static String ImportTblPgm(File kompiled) {
        String filePath = kompiled.getAbsolutePath() + "/Program.tbl";
        if (!tables.contains(filePath)) {
            tables.add(filePath);

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
                    throw KEMException.internalError("Stratego rewriting failed");
                } else {
                    context.setStandAlone(false);
                }
            } catch (StrategoExit exit) {
                context.setStandAlone(false);
                throw KEMException.internalError("Stratego rewriting failed", exit);
            }

            if (result.getTermType() == IStrategoTerm.STRING) {
                rez = (((IStrategoString) result).stringValue());
            } else {
                rez = result.toString();
            }
            return rez;
        }
        return null;
    }

    public synchronized static String ImportTblGround(File kompiled) {
        String filePath = kompiled.getAbsolutePath() + "/Ground.tbl";

        if (!tables.contains(filePath)) {
            tables.add(filePath);

            init();
            String rez = "";
            context.setStandAlone(true);
            IStrategoTerm result = null;
            try {
                try {
                    result = context.invokeStrategyCLI(import$Tbl$Ground_0_0.instance, "a.exe", filePath);
                } finally {
                    context.getIOAgent().closeAllFiles();
                }
                if (result == null) {
                    System.err.println("rewriting failed, trace:");
                    context.printStackTrace();
                    context.setStandAlone(false);
                    throw KEMException.internalError("Stratego rewriting failed");
                } else {
                    context.setStandAlone(false);
                }
            } catch (StrategoExit exit) {
                context.setStandAlone(false);
                throw KEMException.internalError("Stratego rewriting failed", exit);
            }

            if (result.getTermType() == IStrategoTerm.STRING) {
                rez = (((IStrategoString) result).stringValue());
            } else {
                rez = result.toString();
            }
            return rez;
        }
        return null;
    }

    public synchronized static String ParseKoreString(String kDefinition) {
        init();
        String rez = "";
        context.setStandAlone(true);
        IStrategoTerm result = null;
        try {
            try {
                result = context.invokeStrategyCLI(java$Parse$String$Kore_0_0.instance, "a.exe", kDefinition);
            } finally {
                context.getIOAgent().closeAllFiles();
            }
            if (result == null) {
                System.err.println("Input: " + kDefinition);
                System.err.println("rewriting failed, trace:");
                context.printStackTrace();
                context.setStandAlone(false);
                throw KEMException.internalError("Stratego rewriting failed");
            } else {
                context.setStandAlone(false);
            }
        } catch (StrategoExit exit) {
            context.setStandAlone(false);
            throw KEMException.internalError("Stratego rewriting failed", exit);
        }

        if (result.getTermType() == IStrategoTerm.STRING) {
            rez = (((IStrategoString) result).stringValue());
        } else {
            rez = result.toString();
        }
        return rez;
    }

    public synchronized static String ParseKConfigString(String kDefinition) {
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
                throw KEMException.internalError("Stratego rewriting failed");
            } else {
                context.setStandAlone(false);
            }
        } catch (StrategoExit exit) {
            context.setStandAlone(false);
            throw KEMException.internalError("Stratego rewriting failed", exit);
        }

        if (result.getTermType() == IStrategoTerm.STRING) {
            rez = (((IStrategoString) result).stringValue());
        } else {
            rez = result.toString();
        }
        return rez;
    }

    public synchronized static String ParseKRuleString(String kDefinition) {
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
                System.err.println("Input: " + kDefinition);
                System.err.println("rewriting failed, trace:");
                context.printStackTrace();
                context.setStandAlone(false);
                throw KEMException.internalError("Stratego rewriting failed");
            } else {
                context.setStandAlone(false);
            }
        } catch (StrategoExit exit) {
            context.setStandAlone(false);
            throw KEMException.internalError("Stratego rewriting failed", exit);
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
    public synchronized static String ParseKCmdString(String argument) {
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
                System.err.println("Input: " + argument);
                System.err.println("rewriting failed, trace:");
                context.printStackTrace();
                context.setStandAlone(false);
                throw KEMException.internalError("Stratego rewriting failed");
            } else {
                context.setStandAlone(false);
            }
        } catch (StrategoExit exit) {
            context.setStandAlone(false);
            throw KEMException.internalError("Stratego rewriting failed", exit);
        }

        if (result.getTermType() == IStrategoTerm.STRING) {
            rez = (((IStrategoString) result).stringValue());
        } else {
            rez = result.toString();
        }
        return rez;
    }

    public synchronized static String ParseProgramString(String program, String startSymbol) {
        init();
        String rez = "";
        context.setStandAlone(true);
        IStrategoTerm result = null;
        try {
            try {
                result = context.invokeStrategyCLI(java$Parse$String$Pgm_0_0.instance, StringUtil.escapeSort(startSymbol), program);
            } finally {
                context.getIOAgent().closeAllFiles();
            }
            if (result == null) {
                System.err.println("rewriting failed, trace:");
                context.printStackTrace();
                context.setStandAlone(false);
                throw KEMException.internalError("Stratego rewriting failed");
            } else {
                context.setStandAlone(false);
            }
        } catch (StrategoExit exit) {
            context.setStandAlone(false);
            throw KEMException.internalError("Stratego rewriting failed", exit);
        }

        if (result.getTermType() == IStrategoTerm.STRING) {
            rez = (((IStrategoString) result).stringValue());
        } else {
            rez = result.toString();
        }
        return rez;
    }
}

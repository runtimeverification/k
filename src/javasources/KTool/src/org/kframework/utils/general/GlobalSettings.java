// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.utils.general;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.KPaths;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class GlobalSettings {

    public static File getNativeExecutable(String executable) {
        File f = null;
        String basePath = KPaths.getKBase(false);

        switch (GlobalSettings.os()) {
            case UNIX:
                f = new File(basePath + "/lib/native/linux/" + executable);
                f.setExecutable(true, false);
                break;
            case WIN:
                f = new File(basePath + "/lib/native/cygwin/" + executable + ".exe");
                break;
            case OSX:
                f = new File(basePath + "/lib/native/macosx/" + executable);
                f.setExecutable(true, false);
                break;
            default:
                System.err.println("Unknown OS type. " + System.getProperty("os.name") + " not recognized.");
                // abort
                System.exit(1);
        }

        return f;
    }

    public static void setMainFile(String def) {
        mainFile = new File(def);
        mainFileWithNoExtension = mainFile.getAbsolutePath().replaceFirst("\\.k$", "").replaceFirst("\\.xml$", "");
        if (!mainFile.exists()) {
            File errorFile = mainFile;
            mainFile = new File(def + ".k");
            if (!mainFile.exists()) {
                String msg = "File: " + errorFile.getName() + "(.k) not found.";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, errorFile.getAbsolutePath(), "File system."));
            }
        }
    }

    public enum OS {
        OSX, UNIX, UNKNOWN, WIN
    }

    private static OS os = null;
    public static boolean verbose = false;
    public static String lib = "";
    public static String synModule = null;
    public static KExceptionManager kem = new KExceptionManager();
    public static File mainFile;
    public static String mainFileWithNoExtension;
    public static String outputDir;
    public static String warnings = "normal";
    public static List<String> transition = new ArrayList<String>();
    public static List<String> superheat = new ArrayList<String>();
    public static List<String> supercool = new ArrayList<String>();
    public static List<String> doctags = new ArrayList<String>();

    
    public static final String TRANSITION = "transition";

    static {
        transition.add(TRANSITION);
        superheat.add("superheat");
        supercool.add("supercool");
        doctags.add("documentation");
    }
    public static boolean addTopCell = false;
    public static String style = "poster,style=bubble";
    public static boolean fastKast = false;
    public static boolean noPrelude = false;
    
    // this is used by kast to know what parser to use fort the input string
    public static ParserType whatParser = ParserType.PROGRAM;

    public static OS os() {
        if (os == null) {
            String osString = System.getProperty("os.name").toLowerCase();
            if (osString.contains("nix") || osString.contains("nux")) os = OS.UNIX;
            else if (osString.contains("win")) os = OS.WIN;
            else if (osString.contains("mac")) os = OS.OSX;
            else os = OS.UNKNOWN;
        }
        return os;
    }

    public static boolean isWindowsOS() {
        return os() == OS.WIN;
    }

    public static boolean isPosix() {
        return os() == OS.UNIX || os() == OS.OSX;
    }

    public enum ParserType {
        PROGRAM, GROUND, RULES, BINARY, NEWPROGRAM
    }

    //the type of rule indexing rule to use during kompile
    public static String ruleIndex = "table";

    public static boolean symbolicEquality = false;
    public static boolean SMT = false;
    public static boolean javaBackend = false;
    public static boolean documentation = false;
    public static boolean NOSMT = false;

    //needed for test generation in Java backend
    public static boolean testgen = false;
    
    public static String CHECK = null;
    public static boolean symbolic = false; // true if the --symbolic argument has been provided to kompile
    public static List<String> symbolicTags = new LinkedList<>();
    public static List<String> nonSymbolicTags = new LinkedList<>();
}

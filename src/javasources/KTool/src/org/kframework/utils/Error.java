package org.kframework.utils;

import java.io.File;

import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;

import java.util.Comparator;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class Error {

    public static void report(String message) {
        System.out.println("Error: " + message);
        System.exit(1);
    }

    public static void silentReport(String localizedMessage) {
        System.out.println("Warning: " + localizedMessage);
    }

    public static void helpExit(HelpFormatter help, Options options) {
        helpExit(help, "help", options);
    }

    public static void helpExit(HelpFormatter help, String cmdLineSyntax, Options options) {
        System.out.println("\n");
        help.printHelp(cmdLineSyntax, "\nCompiles the K definitions given as arguments.\n\n", options, "\n", true);
        System.out.println("\n");
        System.exit(1);
    }

    public static void helpMsg(String usage, String header, String footer, Options options, Comparator comparator) {
        HelpFormatter helpFormatter = new HelpFormatter();
        helpFormatter.setOptionComparator(comparator);
        helpFormatter.setWidth(79);
        helpFormatter.printHelp(usage, header, options, footer);
        System.out.println();
        //System.exit(1);
    }

    public static void checkIfInputDirectory(String directory) {
        if (!new File(directory).isDirectory()) {
            String msg = "Does not exist or not a directory: " + directory;
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "", ""));
        }
    }
    public static void checkIfOutputDirectory(File directory) {
        if (directory.isFile()) { // isFile = exists && !isDirectory
            String msg = "Not a directory: " + directory;
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "", ""));
        }
    }
}

// vim: noexpandtab

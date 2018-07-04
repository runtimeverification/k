// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework;

import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kprove.KProveOptions;
import org.kframework.krun.KRun;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.OutputModes;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import org.apache.commons.io.output.WriterOutputStream;

import java.util.Set;
import java.util.ArrayList;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.lang.Math;

public class Debugg {

    // *ALL* `public` methods *MUST* return `void` and have their first line be `if (! Debugg.loggingOn) return;`
    private static FileUtil files;
    private static Module   specModule;
    private static Module   parsingModule;
    private static KPrint   kprint;
    private static boolean  loggingOn;

    private static String      loggingPath;
    private static String      sessionId;
    private static File        sessionDir;
    private static File        nodesDir;
    private static PrintWriter sessionLog;
    private static String      currentTerm;
    private static String      currentRule;
    private static long        startTime;

    public static void init(KProveOptions kproveOptions, FileUtil files, Module specModule, Module parsingModule, KPrint kprint) {
        Debugg.loggingOn = kproveOptions.debugg;
        if (! Debugg.loggingOn) return;

        Debugg.files         = files;
        Debugg.specModule    = specModule;
        Debugg.parsingModule = parsingModule;
        Debugg.kprint        = kprint;

        Debugg.loggingPath = kproveOptions.debuggPath;
        try {
            Debugg.sessionId  = Integer.toString(Math.abs(Debugg.specModule.hashCode()));
            Debugg.sessionDir = kproveOptions.debuggPath == null ? files.resolveKompiled(sessionId + ".debugg") : new File(kproveOptions.debuggPath);
            String path       = sessionDir.getAbsolutePath();
            Debugg.nodesDir   = new File(Debugg.sessionDir, "nodes/");
            Debugg.nodesDir.mkdirs();
            Debugg.sessionLog = new PrintWriter(Debugg.sessionDir.getAbsolutePath() + "/debugg.log");
            System.out.println("Debugg: " + Debugg.sessionDir.getAbsolutePath());
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }

        if (Debugg.kprint.options.output == OutputModes.PRETTY) {
            System.err.println("Cannot output in `pretty` mode when using Debugg. Defaulting to `json`.");
            Debugg.kprint.options.output = OutputModes.JSON;
        }

        Debugg.currentTerm = "NOTERM";
        Debugg.currentRule = "NORULE";
        Debugg.startTime   = System.currentTimeMillis();
    }

    public static enum LogEvent {
        INIT, TARGET, IMPLIESTARGET, NODE, MARKEDNODE, RULE, SRSTEP, BRANCH, IMPLICATION, Z3QUERY, Z3RESULT, STEP, RSTEP, CRASH
    }

    public static void log(String logItem) {
        if (! Debugg.loggingOn) return;
        Debugg.sessionLog.println((System.currentTimeMillis() - Debugg.startTime) + " " + logItem);
        Debugg.sessionLog.flush();
    }

    public static void log(LogEvent logCode, K... terms) {
        if (! Debugg.loggingOn) return;
        ArrayList<String> nodeIds = new ArrayList<String>();
        for (K term: terms) {
            nodeIds.add(writeNode(term));
        }
        String nodeId = String.join("_", nodeIds);
        String logPrefix = "";
        switch(logCode) {
            case INIT:
                currentTerm = nodeId;
                logPrefix = "init";
                break;
            case TARGET:
                logPrefix = "target";
                break;
            case IMPLIESTARGET:
                logPrefix = "finished";
                break;
            case NODE:
                currentTerm = nodeId;
                logPrefix = "node";
                break;
            case MARKEDNODE:
                currentTerm = nodeId;
                logPrefix = "markednode";
                break;
            case RULE:
                currentRule = nodeId;
                logPrefix = "rule";
                break;
            case SRSTEP:
                logPrefix = "srstep " + currentRule;
                break;
            case RSTEP:
                logPrefix = "rstep " + currentRule;
                break;
            case BRANCH:
                logPrefix = "branch";
                break;
            case IMPLICATION:
                logPrefix = "implication";
                break;
            case Z3QUERY:
                logPrefix = "z3query";
                break;
            case Z3RESULT:
                logPrefix = "z3result";
                break;
            case STEP:
                logPrefix = "step";
                break;
            case CRASH:
                logPrefix = "crash";
                break;
        }
        Debugg.log(logPrefix + " " + currentTerm + " " + nodeId);
    }

    public static void close() {
        if (! Debugg.loggingOn) return;
        Debugg.sessionLog.close();
    }

    private static String writeNode(K contents) {
        String fileCode   = Integer.toString(Math.abs(contents.hashCode()));
        File   outputFile = new File(Debugg.nodesDir, fileCode + "." + Debugg.kprint.options.output.ext());
        if (! outputFile.exists()) {
            try {
                PrintWriter fOut = new PrintWriter(outputFile);
                fOut.println(new String(Debugg.kprint.prettyPrint(Debugg.parsingModule, contents), StandardCharsets.UTF_8));
                fOut.close();
            } catch (FileNotFoundException e) {
                System.err.println("Could not open node output file: " + outputFile.getAbsolutePath());
                e.printStackTrace();
            }
        }
        return fileCode;
    }
}

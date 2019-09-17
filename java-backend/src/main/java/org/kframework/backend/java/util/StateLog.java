// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.krun.KRun;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.unparser.KPrint;
import org.kframework.unparser.OutputModes;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.OutputStream;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import org.apache.commons.io.output.WriterOutputStream;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.lang.Math;

public class StateLog {

    // *ALL* `public` methods *MUST* return `void` and have their first line be `if (! this.loggingOn) return;`
    private final boolean        loggingOn;
    private final File           loggingPath;
    private final File           blobsDir;
    private final List<LogEvent> logEvents;

    private String              sessionId;
    private PrintWriter         sessionLog;
    private PrettyPrinter       prettyPrinter;
    private Map<Integer,String> writtenHashes;

    private boolean inited;
    private long    startTime;

    public StateLog() {
        this.inited        = false;
        this.loggingOn     = false;
        this.loggingPath   = null;
        this.blobsDir      = null;
        this.logEvents     = Collections.emptyList();
        this.prettyPrinter = null;
        this.writtenHashes = new HashMap<Integer,String>();
    }

    public StateLog(JavaExecutionOptions javaExecutionOptions, FileUtil files, PrettyPrinter prettyPrinter) {
        this.inited    = false;
        this.loggingOn = javaExecutionOptions.stateLog;

        this.loggingPath = javaExecutionOptions.stateLogPath == null
                         ? files.resolveKompiled("stateLog")
                         : new File(javaExecutionOptions.stateLogPath);

        if (javaExecutionOptions.stateLogId != null) this.sessionId = javaExecutionOptions.stateLogId;

        this.blobsDir = new File(loggingPath, this.sessionId + "_blobs/");
        this.blobsDir.mkdirs();

        this.logEvents     = javaExecutionOptions.stateLogEvents;
        this.prettyPrinter = prettyPrinter;
        this.writtenHashes = new HashMap<Integer,String>();
    }

    public void open(String defaultSessionId) {
        if ((! this.loggingOn) || this.inited) return;
        this.inited = true;
        boolean sessionIdNotSet = this.sessionId == null;
        if (sessionIdNotSet) this.sessionId = defaultSessionId;
        File logFile = new File(this.loggingPath, this.sessionId + ".log");
        PrintWriter sessionLog;
        try {
            this.sessionLog = new PrintWriter(logFile);
            if(sessionIdNotSet) System.out.println("StateLog: " + logFile);
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
        this.startTime = System.currentTimeMillis();
        this.log(LogEvent.OPEN);
    }

    public static enum LogEvent {
        OPEN, REACHINIT, REACHTARGET, REACHPROVED, REACHUNPROVED, EXECINIT, SEARCHINIT, SEARCHREACH, NODE, RULE, SRULE, RULEATTEMPT, SRULEATTEMPT, IMPLICATION, Z3QUERY, Z3RESULT, CLOSE, CHECKINGCONSTRAINT
    }

    public void log(String logItem) {
        if (! this.loggingOn) return;
        this.sessionLog.println((System.currentTimeMillis() - this.startTime) + " " + logItem);
        this.sessionLog.flush();
    }

    public void log(LogEvent logCode, K... terms) {
        if (! (this.loggingOn && this.logEvents.contains(logCode))) return;
        ArrayList<String> nodeIds = new ArrayList<String>();
        for (K term: terms) {
            nodeIds.add(writeNode(term));
        }
        String nodeId = String.join("_", nodeIds);
        this.log(logCode.toString() + " " + nodeId);
    }

    public void close() {
        if (! this.loggingOn) return;
        this.log(LogEvent.CLOSE);
        this.sessionLog.close();
    }

    private static String hash(K in) {
        MessageDigest m = null;
        String hashtext = "__";
        try {
            m = MessageDigest.getInstance("MD5");
            m.reset();
            m.update(KPrint.serialize(in, OutputModes.KAST));
            byte[] digest = m.digest();
            BigInteger bigInt = new BigInteger(1,digest);
            hashtext = bigInt.toString(16);
        } catch (NoSuchAlgorithmException e) {
            e.printStackTrace();
        }
        return hashtext;
    }

    private String writeNode(K contents) {
        int objectHash = contents.hashCode();
        if (writtenHashes.containsKey(objectHash)) {
            return writtenHashes.get(objectHash);
        } else {
            String fileCode   = hash(contents);
            File   outputFile = new File(this.blobsDir, fileCode + "." + OutputModes.JSON.ext());
            if (! outputFile.exists()) {
                try {
                    String out = new String(this.prettyPrinter.prettyPrintBytes(contents), StandardCharsets.UTF_8);
                    PrintWriter fOut = new PrintWriter(outputFile);
                    fOut.println(out);
                    fOut.close();
                    writtenHashes.put(objectHash,fileCode);
                } catch (FileNotFoundException e) {
                    System.err.println("Could not open node output file: " + outputFile.getAbsolutePath());
                    e.printStackTrace();
                }
            }
            return fileCode;
        }
    }
}

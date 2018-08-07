// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.ImmutableSet;
import org.kframework.backend.java.z3.*;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.OS;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.SMTOptions;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.Set;

/**
 * @author Traian
 */
public class Z3Wrapper {

    private static final int Z3_RESTART_LIMIT = 3;

    public static final Set<String> Z3_QUERY_RESULTS = ImmutableSet.of("unknown", "sat", "unsat");

    public final String SMT_PRELUDE, CHECK_SAT;
    private final SMTOptions options;
    private final GlobalOptions globalOptions;
    private final KExceptionManager kem;
    private final FileUtil files;

    public Z3Wrapper(
            SMTOptions options,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            FileUtil files) {
        this.options = options;
        this.kem = kem;
        this.globalOptions = globalOptions;
        this.files = files;

        String defaultPrelude = "(set-option :auto-config false)\n"
                              + "(set-option :smt.mbqi false)\n";

        SMT_PRELUDE = options.smtPrelude == null ? defaultPrelude : files.loadFromWorkingDirectory(options.smtPrelude);
        CHECK_SAT = options.z3Tactic == null ? "(check-sat)" : "(check-sat-using " + options.z3Tactic + ")";
    }

    public synchronized boolean isUnsat(CharSequence query, int timeout, Z3Profiler timer) {
        if (options.z3JNI) {
            return checkQueryWithLibrary(query, timeout);
        } else {
            return checkQueryWithExternalProcess(query, timeout, timer);
        }
    }

    private boolean checkQueryWithLibrary(CharSequence query, int timeout) {
        boolean result = false;
        try (Z3Context context = new Z3Context()) {
            Z3Solver solver = new Z3Solver(context);
            Z3Params params = new Z3Params(context);
            params.add("timeout", timeout);
            solver.setParams(params);
            solver._assert(context.parseSmtlib2(SMT_PRELUDE + query));
            result = solver.check() == Z3Status.UNSAT;
        } catch (Z3Exception e) {
            kem.registerCriticalWarning(
                    "failed to translate smtlib expression:\n" + SMT_PRELUDE + query, e);
        } catch (UnsatisfiedLinkError e) {
            System.err.println(System.getProperty("java.library.path"));
            throw e;
        }
        return result;
    }

    /**
     * @return true if query result is unsat, false otherwise.
     */
    private boolean checkQueryWithExternalProcess(CharSequence query, int timeout, Z3Profiler profiler) {
        String result = "";
        profiler.startQuery();
        try {
            for (int i = 0; i < Z3_RESTART_LIMIT; i++) {
                ProcessBuilder pb = files.getProcessBuilder().command(
                        OS.current().getNativeExecutable("z3"),
                        "-in",
                        "-smt2",
                        "-t:" + timeout);
                pb.redirectInput(ProcessBuilder.Redirect.PIPE);
                pb.redirectOutput(ProcessBuilder.Redirect.PIPE);
                profiler.startRun();
                Process z3Process = pb.start();
                PrintWriter input = new PrintWriter(z3Process.getOutputStream());
                BufferedReader output = new BufferedReader(new InputStreamReader(z3Process.getInputStream()));
                input.format("%s%s%s\n", SMT_PRELUDE, query, CHECK_SAT);
                input.close();
                result = null;
                String line = output.readLine();
                while (line != null && line.startsWith("(error")) {
                    System.err.println("\nZ3 error: " + line);
                    result = line;
                    line = output.readLine();
                }
                if (line != null) {
                    result = line;
                }
                z3Process.destroy();
                profiler.endRun(timeout);
                if (result != null) {
                    break;
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            if (globalOptions.debugZ3 && profiler.isLastRunTimeout()) {
                System.err.println("\nZ3 likely timeout");
            }
        }
        if (!Z3_QUERY_RESULTS.contains(result)) {
            throw KEMException.criticalError("Z3 crashed on input query:\n" + query + "\nresult:\n" + result);
        }
        if (globalOptions.debugZ3) {
            System.err.println("\nZ3 query result: " + result);
        }
        profiler.queryResult(result);
        return "unsat".equals(result);
    }
}


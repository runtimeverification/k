// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.base.Charsets;
import com.google.common.collect.ImmutableSet;
import com.google.common.io.Files;
import com.google.inject.Inject;
import com.google.inject.Provider;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.kframework.main.GlobalOptions;
import org.kframework.utils.OS;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.options.SMTOptions;

import java.io.*;
import java.util.Set;

/**
 * @author Traian
 */
public class Z3Wrapper {

    private static final int Z3_RESTART_LIMIT = 3;

    private static final Set<String> Z3_QUERY_RESULTS = ImmutableSet.of("unknown", "sat", "unsat");

    public final String SMT_PRELUDE;
    private final SMTOptions options;
    private final GlobalOptions globalOptions;
    private final KExceptionManager kem;
    private final Provider<ProcessBuilder> pb;

    @Inject
    public Z3Wrapper(
            SMTOptions options,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            Provider<ProcessBuilder> pb) {
        this.options = options;
        this.kem = kem;
        this.globalOptions = globalOptions;
        this.pb = pb;

        String s = "";
        try {
            if (options.smtPrelude() != null) {
                s = Files.toString(options.smtPrelude(), Charsets.UTF_8);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        SMT_PRELUDE = s;
    }

    public boolean checkQuery(String query, int timeout) {
        if (options.z3Executable) {
            return checkQueryWithExternalProcess(query, timeout);
        } else {
            return checkQueryWithLibrary(query, timeout);
        }
    }

    public boolean checkQueryWithLibrary(String query, int timeout) {
        boolean result = false;
        try {
            com.microsoft.z3.Context context = new com.microsoft.z3.Context();
            Solver solver = context.mkSolver();
            Params params = context.mkParams();
            params.add("timeout", timeout);
            solver.setParameters(params);
            solver.add(context.parseSMTLIB2String(SMT_PRELUDE + query, null, null, null, null));
            result = solver.check() == Status.UNSATISFIABLE;
            context.dispose();
        } catch (Z3Exception e) {
            kem.registerCriticalWarning(
                    "failed to translate smtlib expression:\n" + SMT_PRELUDE + query);
        } catch (UnsatisfiedLinkError e) {
            System.err.println(System.getProperty("java.library.path"));
            throw e;
        }
        return result;
    }

    public boolean checkQueryWithExternalProcess(String query, int timeout) {
        String result = "";
        try {
            for (int i = 0; i < Z3_RESTART_LIMIT; i++) {
                ProcessBuilder pb = this.pb.get().command(
                        OS.current().getNativeExecutable("z3"),
                        "-in",
                        "-smt2",
                        "-t:" + timeout);
                pb.redirectInput(ProcessBuilder.Redirect.PIPE);
                pb.redirectOutput(ProcessBuilder.Redirect.PIPE);
                Process z3Process = pb.start();
                BufferedWriter input = new BufferedWriter(new OutputStreamWriter(
                    z3Process.getOutputStream()));
                BufferedReader output = new BufferedReader(new InputStreamReader(
                    z3Process.getInputStream()));
                input.write(SMT_PRELUDE + query + "(check-sat)\n");
                input.flush();
                result = output.readLine();
                z3Process.destroy();

                if (result != null) {
                    break;
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        if (result == null) {
            result = "unknown";
            if (globalOptions.debug) {
                System.err.println("Z3 crashed on query:\n" + SMT_PRELUDE + query + "(check-sat)\n");
            }
        } else if (result != null) {
            if (globalOptions.debug && !Z3_QUERY_RESULTS.contains(result)) {
                System.err.println("Unexpected Z3 query result:\n" + result);
            }
        }
        return result.equals("unsat");
    }
}


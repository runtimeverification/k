// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.ImmutableSet;
import com.google.inject.Inject;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.OS;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.SMTOptions;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
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
    private final FileUtil files;

    @Inject
    public Z3Wrapper(
            SMTOptions options,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            FileUtil files) {
        this.options = options;
        this.kem = kem;
        this.globalOptions = globalOptions;
        this.files = files;

        SMT_PRELUDE = options.smtPrelude == null ? "" : files.loadFromWorkingDirectory(options.smtPrelude);
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
                ProcessBuilder pb = files.getProcessBuilder().command(
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


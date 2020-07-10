// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.ImmutableSet;
import org.apache.commons.io.IOUtils;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.z3.Z3Context;
import org.kframework.backend.java.z3.Z3Exception;
import org.kframework.backend.java.z3.Z3Params;
import org.kframework.backend.java.z3.Z3Solver;
import org.kframework.backend.java.z3.Z3Status;
import org.kframework.builtin.Sorts;
import org.kframework.utils.OS;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.SMTOptions;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.Set;

import static org.kframework.kore.KORE.*;

/**
 * @author Traian
 */
public class Z3Wrapper {

    public static final Set<String> Z3_QUERY_RESULTS = ImmutableSet.of("unknown", "sat", "unsat");

    public final String SMT_PRELUDE, CHECK_SAT;
    private final SMTOptions options;
    private final JavaExecutionOptions javaExecutionOptions;
    private final KExceptionManager kem;
    private final FileUtil files;
    private final StateLog stateLog;
    private final GlobalContext global;

    public Z3Wrapper(
            SMTOptions options,
            KExceptionManager kem,
            JavaExecutionOptions javaExecutionOptions,
            FileUtil files,
            StateLog stateLog, GlobalContext globalContext) {
        this.options = options;
        this.kem = kem;
        this.javaExecutionOptions = javaExecutionOptions;
        this.files = files;
        this.stateLog = stateLog;
        this.global = globalContext;

        String defaultPrelude = ""
                + "(set-option :auto-config false)\n"
                + "(set-option :smt.mbqi false)\n";

        SMT_PRELUDE = options.smtPrelude == null ? defaultPrelude : files.loadFromWorkingDirectory(options.smtPrelude);
        CHECK_SAT = options.z3Tactic == null ? "(check-sat)" : "(check-sat-using " + options.z3Tactic + ")";
    }

    public synchronized boolean isUnsat(CharSequence query, int timeout, Z3Profiler timer) {
        stateLog.log(StateLog.LogEvent.Z3QUERY,
                KToken(SMT_PRELUDE + "\n" + query + "\n" + CHECK_SAT + "\n", Sorts.Z3Query()));
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
            kem.registerCriticalWarning(ExceptionType.PROOF_LINT,
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
        String result;
        profiler.startQuery();
        try {
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
            input.format("%s%s%s\n", SMT_PRELUDE, query, CHECK_SAT);
            input.close();
            // When the process dies, that input stream does not go away automatically.
            // https://stackoverflow.com/a/7100172/4182868
            result = IOUtils.toString(z3Process.getInputStream()).trim();
            z3Process.destroy();
            profiler.endRun(timeout);

            if (result.isEmpty()) {
                result = "Z3 error: ended with no output";
            }
        } catch (IOException e) {
            throw KEMException.criticalError("Exception while invoking Z3", e);
        } finally {
            if (javaExecutionOptions.debugZ3 && profiler.isLastRunTimeout()) {
                //In case of timeout, result is "unknown", so evaluation can proceed.
                global.log().format("\nZ3 likely timeout\n");
            }
        }
        stateLog.log(StateLog.LogEvent.Z3RESULT, KToken(result, Sorts.Z3Result()));
        if (!Z3_QUERY_RESULTS.contains(result)) {
            throw KEMException.criticalError("Z3 crashed on input query:\n" + query + "\nresult:\n" + result);
        }
        if (javaExecutionOptions.debugZ3) {
            global.log().format("\nZ3 query result: %s\n", result);
        }
        profiler.queryResult(result);
        return "unsat".equals(result);
    }
}

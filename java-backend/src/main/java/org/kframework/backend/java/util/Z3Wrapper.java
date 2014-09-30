// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.io.Files;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.kframework.kil.loader.Context;
import org.kframework.utils.OS;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;

/**
 * @author Traian
 */
public class Z3Wrapper {

    public static Z3Wrapper Z3_WRAPPER;
    public static Z3Wrapper instance(Context context) {
        if (Z3_WRAPPER == null) {
            Z3_WRAPPER = new Z3Wrapper(context);
        }
        return Z3_WRAPPER;
    }

    public final String SMT_PRELUDE;

    public Z3Wrapper(Context context) {
        String s = "";
        try {
            if (context.krunOptions.experimental.smtPrelude() != null) {
                s = new String(Files.toByteArray(context.krunOptions.experimental.smtPrelude()));
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        SMT_PRELUDE = s;
    }

    public boolean checkQuery(String query, int timeout, Context context) {
        if (context.krunOptions.experimental.z3Executable) {
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
            GlobalSettings.kem.registerCriticalWarning(
                    "failed to translate smtlib expression:\n" + SMT_PRELUDE + query);
        }
        return result;
    }

    public boolean checkQueryWithExternalProcess(String query, int timeout) {
        String result = "";
        try {
            do {
                ProcessBuilder pb = new ProcessBuilder(
                        OS.current().getNativeExecutable("z3").getAbsolutePath(),
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
            } while (result == null);
        } catch (IOException e) {
            e.printStackTrace();
        }
        return result.equals("unsat");
    }
}


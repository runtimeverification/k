// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.io.Files;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.kframework.kil.loader.Context;
import java.io.IOException;

/**
 * @author Traian
 */
public class Z3Wrapper {

    public static boolean initialized = false;

    public static Z3Wrapper Z3_WRAPPER;
    public static Z3Wrapper instance(Context context) {
        if (Z3_WRAPPER == null) {
            Z3_WRAPPER = new Z3Wrapper(context);
        }
        return Z3_WRAPPER;
    }

    public final String SMT_PRELUDE;
    private String logic;

    public Z3Wrapper(Context context) {
        String s = "";
        try {
            if (context.krunOptions.experimental.smtPrelude() != null) {
                s = new String(Files.toByteArray(context.krunOptions.experimental.smtPrelude()));
                logic = context.krunOptions.experimental.smtPrelude().getName().equals("floating_point.smt2") ? "QF_FPA" : null;
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        SMT_PRELUDE = s;
    }

    public boolean checkQuery(String query) {
        boolean result = false;
        try {
            com.microsoft.z3.Context context = new com.microsoft.z3.Context();
            Solver solver = logic != null ? context.mkSolver(logic) : context.mkSolver();
            solver.add(context.parseSMTLIB2String(SMT_PRELUDE + query, null, null, null, null));
            result = solver.check() == Status.UNSATISFIABLE;
            context.dispose();
        } catch (Z3Exception e) {
            System.err.println("failed to translate smtlib expression:\n" + SMT_PRELUDE + query);
            e.printStackTrace();
        }
        return result;
    }
}


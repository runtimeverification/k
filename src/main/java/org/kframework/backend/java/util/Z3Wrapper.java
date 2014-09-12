// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.io.Files;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.kframework.utils.file.JarInfo;

import java.io.File;
import java.io.IOException;

/**
 * @author Traian
 */
public class Z3Wrapper {

    public static boolean initialized = false;

    public static final Z3Wrapper Z3_WRAPPER = new Z3Wrapper();
    public static Z3Wrapper instance() {
        return Z3_WRAPPER;
    }

    public final String SMT_PRELUDE;

    public Z3Wrapper() {
        String s = "";
        try {
            s = new String(Files.toByteArray(new File(JarInfo.getZ3PreludePath())));
        } catch (IOException e) {
            e.printStackTrace();
        }
        SMT_PRELUDE = s;
    }

    public boolean checkQuery(String query) {
        boolean result = false;
        try {
            com.microsoft.z3.Context context = new com.microsoft.z3.Context();
            Solver solver = context.mkSolver();
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


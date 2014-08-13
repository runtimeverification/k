// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.kframework.utils.OS;
import org.kframework.utils.file.KPaths;

import java.io.File;

/**
 * @author Traian
 */
public class Z3Wrapper {
    public static boolean initialized = false;
    public static com.microsoft.z3.Context newContext() throws Z3Exception {
        if (!initialized) {
            String libz3 = "libz3";
            switch (OS.current()) {
                case WIN:
                    libz3 += ".dll";
                    break;
                case UNIX:
                    libz3 += ".so";
                    break;
                case OSX:
                    libz3 += ".dylib";
            }
            System.load(KPaths.getJavaLibraryPath() + File.separator + libz3);
            initialized = true;
        }
        return new com.microsoft.z3.Context();
    }

    public static boolean checkQuery(String query) {
        boolean result = false;
        try {
            com.microsoft.z3.Context context = newContext();
            Solver solver = context.MkSolver();
            solver.Assert(context.ParseSMTLIB2String(query, null, null, null, null));
            result = solver.Check() == Status.UNSATISFIABLE;
            context.Dispose();
        } catch (Z3Exception e) {
            e.printStackTrace();
        }
        return result;
    }
}

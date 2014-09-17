// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.List;

import org.kframework.backend.java.kil.ConstrainedTerm;

/**
 * Debugger class.
 *
 * @author YilongL
 *
 */
public class Debug {

    public static boolean ENABLE_DEBUG_MODE = false;

    private static int debugMethodCounter = 0;

    public static int incDebugMethodCounter() {
        if (!ENABLE_DEBUG_MODE) {
            return 0;
        }
        return ++debugMethodCounter;
    }

    public static int getDebugMethodCounter() {
        if (!ENABLE_DEBUG_MODE) {
            return 0;
        }
        return debugMethodCounter;
    }

    public static void setBreakPointHere() {
        if (ENABLE_DEBUG_MODE) {
            System.err.println("Set breakpoint here to start debugging...");
        }
    }

    public static void printUnifyResult(int numOfInvoc,
            ConstrainedTerm subject, ConstrainedTerm pattern, List<?> solutions) {
        if (ENABLE_DEBUG_MODE) {
            System.out.printf(
                    "###unify %s###%nsubject = %s%npattern = %s%nsols = %s%n",
                    numOfInvoc, subject, pattern, solutions);
        }
    }

}

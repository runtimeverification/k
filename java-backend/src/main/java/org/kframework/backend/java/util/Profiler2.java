// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.main.Main;

/**
 * @author Denis Bogdanas
 * Created on 23-Jul-18.
 */
public class Profiler2 {
    private static long parsingTimestamp;
    private static long initTimestamp;

    public static final CounterStopwatch resFuncNanoTimer = new CounterStopwatch("resolveFunction");
    public static final CounterStopwatch queryBuildTimer = new CounterStopwatch("Z3 query build");
    public static final Z3Profiler z3Implication = new Z3Profiler("Z3 implication");
    public static final Z3Profiler z3Constraint = new Z3Profiler("Z3 constraint");

    public static void printResult() {
        long currentTimestamp = System.currentTimeMillis();
        System.err.format("Total time:            %.3f\n", (currentTimestamp - Main.startTime) / 1000.);
        System.err.format("  Parsing time:        %.3f\n", (parsingTimestamp - Main.startTime) / 1000.);
        System.err.format("  Initialization time: %.3f\n", (initTimestamp - parsingTimestamp) / 1000.);
        System.err.format("  Execution time:      %.3f\n\n", (currentTimestamp - initTimestamp) / 1000.);

        System.err.format("Init+Execution time:    %.3f\n", (currentTimestamp - parsingTimestamp) / 1000.);
        System.err.format("  query build time:     %s\n", queryBuildTimer);
        z3Constraint.print();
        z3Implication.print();
        System.err.format("  resolveFunction time: %s\n", resFuncNanoTimer);

        System.err.format("resolveFunction top-level calls:   %d\n", resFuncNanoTimer.getCount());

        //Has some overhead. Enable from class Profiler if needed, by setting value below to true.
        if (Profiler.enableProfilingMode.get()) {
            System.err.println("==================");
            Profiler.printResult();
        }
        System.err.println("==================================\n");
    }

    public static void logParsingTime() {
        parsingTimestamp = System.currentTimeMillis();
        System.err.format("\nParsing finished: %.3f s\n", (parsingTimestamp - Main.startTime) / 1000.);
    }

    public static void logInitTime() {
        initTimestamp = System.currentTimeMillis();
        System.err.println("\nInitialization finished\n==================================");
        printResult();
    }
}

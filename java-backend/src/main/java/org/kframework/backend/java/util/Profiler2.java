// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.inject.Inject;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.main.StartTimeHolder;
import org.kframework.utils.inject.RequestScoped;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;

/**
 * @author Denis Bogdanas
 * Created on 23-Jul-18.
 */
@RequestScoped
public class Profiler2 {

    private final long startTime;

    private long parsingTimestamp;
    private long initTimestamp;

    public final CounterStopwatch resFuncNanoTimer = new CounterStopwatch("resolveFunction");
    public final CounterStopwatch logOverheadTimer = new CounterStopwatch("Log");
    public final CounterStopwatch queryBuildTimer = new CounterStopwatch("Z3 query build");

    public int countResFuncTopUncached = 0;
    public int countResFuncRecursiveUncached = 0;
    final Map<FormulaContext.Kind, Z3Profiler> z3Profilers = createZ3Profilers();

    private Map<FormulaContext.Kind, Z3Profiler> createZ3Profilers() {
        BinaryOperator<Z3Profiler> throwingMerger = (u, v) -> {
            throw new IllegalStateException(String.format("Duplicate key %s", u));
        };
        return Arrays.stream(FormulaContext.Kind.values())
                .collect(Collectors.toMap(kind -> kind, kind -> new Z3Profiler("Z3 " + kind.label),
                        throwingMerger, LinkedHashMap::new));
    }

    @Inject
    public Profiler2(StartTimeHolder startTimeHolder) {
        this.startTime = startTimeHolder.getStartTime();
    }

    public void printResult() {
        long currentTimestamp = System.currentTimeMillis();
        System.err.format("Total time:            %.3f\n", (currentTimestamp - startTime) / 1000.);
        System.err.format("  Parsing time:        %.3f\n", (parsingTimestamp - startTime) / 1000.);
        System.err.format("  Initialization time: %.3f\n", (initTimestamp - parsingTimestamp) / 1000.);
        System.err.format("  Execution time:      %.3f\n\n", (currentTimestamp - initTimestamp) / 1000.);

        System.err.format("Init+Execution time:    %.3f\n", (currentTimestamp - parsingTimestamp) / 1000.);
        System.err.format("  query build time:     %s\n", queryBuildTimer);
        for (Z3Profiler profiler : z3Profilers.values()) {
            if (profiler.getQueryCount() > 0) {
                profiler.print();
            }
        }

        System.err.format("  resolveFunction time: %s\n", resFuncNanoTimer);

        System.err.format("resolveFunction top-level calls:   %d\n", resFuncNanoTimer.getCount());

        System.err.format("\nimpliesSMT time:    %s\n", ConjunctiveFormula.impliesStopwatch);
        System.err.format("impliesSMT count: %s\n", ConjunctiveFormula.impliesStopwatch.getCount());

        //Has some overhead. Enable from class Profiler if needed, by setting value below to true.
        if (Profiler.enableProfilingMode.get()) {
            System.err.println("==================");
            Profiler.printResult();
        }
        System.err.println("==================================\n");
    }

    public void logParsingTime() {
        parsingTimestamp = System.currentTimeMillis();
        System.err.format("\nParsing finished: %.3f s\n", (parsingTimestamp - startTime) / 1000.);
    }

    public void logInitTime() {
        initTimestamp = System.currentTimeMillis();
        System.err.println("\nInitialization finished\n==================================");
        printResult();
    }

    public long getStartTime() {
        return startTime;
    }
}

// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.Lists;
import com.google.inject.Inject;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.main.StartTimeHolder;
import org.kframework.utils.inject.RequestScoped;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;

/**
 * @author Denis Bogdanas
 * Created on 23-Jul-18.
 * <p>
 * Reason why explicit GC times are counted separately: they are not included in any other init or execution times, nor
 * in GC time percentage.
 */
@RequestScoped
public class Profiler2 {

    private final JavaExecutionOptions javaExecutionOptions;
    private final TimeMemoryEntry startStats;

    private TimeMemoryEntry parsingStats;
    private TimeMemoryEntry initStats;
    private List<TimeMemoryEntry> cacheMeasuringStats = new ArrayList<>();

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
    public Profiler2(JavaExecutionOptions javaExecutionOptions, StartTimeHolder startTimeHolder) {
        this.javaExecutionOptions = javaExecutionOptions;
        this.startStats = new TimeMemoryEntry(startTimeHolder.getStartTimeNano());
    }

    public void printResult(boolean afterExecution, GlobalContext context) {
        TimeMemoryEntry currentStats = afterExecution ? new TimeMemoryEntry(javaExecutionOptions.profileMemAdv)
                                                      : initStats;
        printStats(currentStats, afterExecution);

        TimeMemoryEntry[] intermediate = getIntermediateStats(initStats);
        System.err.format("\n\nInit+Execution time:    %8.3f s\n",
                currentStats.timeDiff(parsingStats, intermediate));
        if (queryBuildTimer.getCount() > 0) {
            System.err.format("  query build time:     %s\n", queryBuildTimer);
        }
        for (Z3Profiler profiler : z3Profilers.values()) {
            if (profiler.getQueryCount() > 0) {
                profiler.print();
            }
        }

        System.err.format("  resolveFunction time: %s\n", resFuncNanoTimer);
        if (logOverheadTimer.getCount() > 0) {
            System.err.format("  log time:             %s\n", logOverheadTimer);
        }

        if (afterExecution) {
            System.err.format("\nMax memory : %d MB\n", Runtime.getRuntime().maxMemory() / (1024 * 1024));
        }
        printCacheStats(currentStats, afterExecution, context);

        System.err.format("resolveFunction top-level uncached: %d\n", countResFuncTopUncached);
        int countCached = resFuncNanoTimer.getCount() - countResFuncTopUncached;
        if (countCached > 0) {
            System.err.format("resolveFunction top-level cached:   %d\n", countCached);
        }
        System.err.format("resolveFunction recursive uncached: %d\n", countResFuncRecursiveUncached);

        if (ConjunctiveFormula.impliesStopwatch.getCount() > 0) {
            System.err.format("\nimpliesSMT time :    %s\n", ConjunctiveFormula.impliesStopwatch);
            System.err.format("impliesSMT count:    %s\n", ConjunctiveFormula.impliesStopwatch.getCount());
        }

        //Has some overhead. Enable from class Profiler if needed, by setting value below to true.
        if (Profiler.enableProfilingMode.get()) {
            System.err.println("==================");
            Profiler.printResult();
        }
        System.err.println("==================================\n");
    }

    private void printStats(TimeMemoryEntry currentStats, boolean afterExecution) {
        System.err.format("Stats for each phase, time, used memory, implicit main GC time percentage:");
        String postGcPrefix = ",\t\t post-gc mem: ";
        TimeMemoryEntry[] intermediateForTotal = afterExecution ? getIntermediateStats(parsingStats, initStats)
                                                                : getIntermediateStats(parsingStats);
        System.err.format("\nTotal                 : %s%s", currentStats.logString(startStats, intermediateForTotal),
                currentStats.postGCLogString(postGcPrefix, intermediateForTotal));
        System.err.format("\n  Parsing             : %s%s", parsingStats.logString(startStats),
                parsingStats.postGCLogString(postGcPrefix));
        System.err.format("\n  Init                : %s%s", initStats.logString(parsingStats),
                initStats.postGCLogString(postGcPrefix));
        if (afterExecution) {
            System.err.format("\n  Execution           : %s%s",
                    currentStats.logString(initStats, getIntermediateStats()),
                    currentStats.postGCLogString(postGcPrefix, getIntermediateStats()));
        }
    }

    private void printCacheStats(TimeMemoryEntry currentStats, boolean afterExecution, GlobalContext context) {
        //Measure cache after initialization phase only if it's going to be cleared by --cache-func-optimized.
        if (javaExecutionOptions.profileMemAdv &&
                (afterExecution || javaExecutionOptions.cacheFunctionsOptimized)) {
            int funcCacheSize = context.functionCache.size();
            int formulaCacheSize = context.formulaCache.size();
            int toStringCacheSize = context.toStringCache.size();
            context.functionCache.clear();
            TimeMemoryEntry noFuncCache = new TimeMemoryEntry(true);
            System.err.format("Function cache size: %5d MB, %8d entries\n",
                    currentStats.usedPostGCMemory() - noFuncCache.usedPostGCMemory(), funcCacheSize);

            context.formulaCache.clear();
            TimeMemoryEntry noFormulaCache = new TimeMemoryEntry(true);
            System.err.format("Formula cache size : %5d MB, %8d entries\n",
                    noFuncCache.usedPostGCMemory() - noFormulaCache.usedPostGCMemory(), formulaCacheSize);

            context.toStringCache.clear();
            TimeMemoryEntry noToStringCache = new TimeMemoryEntry(true);
            System.err.format("toString cache size: %5d MB, %8d entries\n",
                    noFormulaCache.usedPostGCMemory() - noToStringCache.usedPostGCMemory(), toStringCacheSize);
            System.out.println();

            cacheMeasuringStats = Arrays.asList(noFuncCache, noFormulaCache, noToStringCache);
        }
    }

    private TimeMemoryEntry[] getIntermediateStats(TimeMemoryEntry... mainStats) {
        ArrayList<TimeMemoryEntry> list = Lists.newArrayList(mainStats);
        list.addAll(cacheMeasuringStats);
        return list.toArray(new TimeMemoryEntry[]{});
    }

    public void logParsingTime() {
        parsingStats = new TimeMemoryEntry(javaExecutionOptions.profileMemAdv);
        System.err.format("\nParsing finished: %8.3f s\n", parsingStats.timeDiff(startStats));
    }

    public void logInitTime(GlobalContext context) {
        initStats = new TimeMemoryEntry(javaExecutionOptions.profileMemAdv);
        System.err.println("\nInitialization finished\n==================================");
        printResult(false, context);
    }

    public String stepLogString(TimeMemoryEntry currentStats, TimeMemoryEntry prevStats) {
        return currentStats.stepLogString(initStats, prevStats);
    }
}

// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.Lists;
import com.google.inject.Inject;
import org.kframework.backend.java.kil.GlobalContext;
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

    public final CounterStopwatch resFuncNanoTimer = new CounterStopwatch("resolveFunctionAndAnywhere time");
    public final CounterStopwatch evaluateFunctionNanoTimer = resFuncNanoTimer.newSubTimer("evaluateFunction time");
    public final Counter evalFuncBuiltinCounter = evaluateFunctionNanoTimer.newCounter("builtin evaluation");
    public final Counter evalFuncRuleCounter = evaluateFunctionNanoTimer.newCounter("function rule");
    public final Counter evalFuncSortPredicateCounter = evaluateFunctionNanoTimer.newCounter("sort predicate");
    public final Counter evalFuncOwiseCounter = evaluateFunctionNanoTimer.newCounter("owise rule");
    public final Counter evalFuncNoRuleApplicableCounter = evaluateFunctionNanoTimer.newCounter("no rule applicable");
    public final Counter evalFuncNoRuleCounter = evaluateFunctionNanoTimer.newCounter("no function rules");

    public final CounterStopwatch applyAnywhereRulesNanoTimer = resFuncNanoTimer
            .newSubTimer("applyAnywhereRules time", evaluateFunctionNanoTimer.getSharedLevelHolder());
    public final Counter applyAnywhereBuiltinCounter = applyAnywhereRulesNanoTimer.newCounter("builtin evaluation");
    public final Counter applyAnywhereRuleCounter = applyAnywhereRulesNanoTimer.newCounter("anywhere rule");
    public final Counter applyAnywhereNoRuleApplicableCounter =
            applyAnywhereRulesNanoTimer.newCounter("no rule applicable");
    public final Counter applyAnywhereNoRuleCounter = applyAnywhereRulesNanoTimer.newCounter("no anywhere rules");

    public final CounterStopwatch logOverheadTimer = new CounterStopwatch("log time");
    public final CounterStopwatch queryBuildTimer = new CounterStopwatch("query build time");
    public final CounterStopwatch impliesSMTTimer = new CounterStopwatch("impliesSMT time");

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
        printTimer("  ", queryBuildTimer, null, true);
        for (Z3Profiler profiler : z3Profilers.values()) {
            profiler.print();
        }

        System.err.format("\n  Time and top-level event counts:\n");
        printTimer("  ", resFuncNanoTimer, "remaining time & # cached", true);
        printTimer("  ", logOverheadTimer, null, true);
        printTimer("  ", impliesSMTTimer, null, true);
        System.err.format("\n  Recursive event counts:\n");
        printTimer("  ", resFuncNanoTimer, "# cached", false);

        if (afterExecution) {
            System.err.format("\nMax memory : %d MB\n", Runtime.getRuntime().maxMemory() / (1024 * 1024));
        }
        printCacheStats(currentStats, afterExecution, context);

        //Has some overhead. Enable from class Profiler if needed, by setting value below to true.
        if (Profiler.enableProfilingMode.get()) {
            System.err.println("==================");
            Profiler.printResult();
        }
        System.err.println("==================================\n");
    }

    /**
     * @param topCount true - print top count and time. false - print recursive count and no time.
     */
    public static void printTimer(String prefix, CounterStopwatch timer, String leftoverTimerName, boolean topCount) {
        if (timer.getDuration() == 0 && timer.getCountTop() == 0) {
            return;
        }
        String formatString = "%s%-33s: %10s,      # %10d\n";
        System.err.format(formatString, prefix, timer.getName(), topCount ? timer : "",
                topCount ? timer.getCountTop() : timer.getCountRecursive());
        for (CounterStopwatch subTimer : timer.getSubTimers(leftoverTimerName)) {
            printTimer(prefix + "  ", subTimer, "remaining", topCount);
        }
        for (Counter counter : timer.getCounters("other")) {
            if (counter.getCountTop() > 0) {
                System.err.format(formatString, prefix + "  ", counter.getName(), "",
                        topCount ? counter.getCountTop() : counter.getCountRecursive());
            }
        }
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

    public void logParsingTime(GlobalContext context) {
        parsingStats = new TimeMemoryEntry(javaExecutionOptions.profileMemAdv);
        if (context.globalOptions.verbose) {
            System.err.format("\nParsing finished: %8.3f s\n", parsingStats.timeDiff(startStats));
        }
    }

    public void logInitTime(GlobalContext context) {
        initStats = new TimeMemoryEntry(javaExecutionOptions.profileMemAdv);
        if (context.globalOptions.verbose) {
            System.err.println("\nInitialization finished\n==================================");
            printResult(false, context);
        }
    }

    public String stepLogString(TimeMemoryEntry currentStats, TimeMemoryEntry prevStats) {
        return currentStats.stepLogString(initStats, prevStats);
    }
}

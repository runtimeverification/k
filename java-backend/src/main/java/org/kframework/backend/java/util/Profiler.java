// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.concurrent.TimeUnit;

import org.apache.commons.collections4.comparators.ReverseComparator;
import org.kframework.backend.java.kil.KLabelConstant;

import com.google.common.base.Stopwatch;

/**
 * Profiling class.
 * <p>
 * TODO(YilongL): for now, it's only used for profiling krun without search; I
 * will need to refactor it later to make it general.
 *
 * @author YilongL
 *
 */
public class Profiler {

    public static final InheritableThreadLocal<Boolean> enableProfilingMode = new InheritableThreadLocal<Boolean>() {
        @Override
        protected Boolean initialValue() {
            return false;
        }
    };

    public static final ReentrantStopwatch QUERY_RULE_INDEXING_TIMER            =   new ReentrantStopwatch("Query rule indexing");
    public static final ReentrantStopwatch REWRITE_WITH_KOMPILED_RULES_TIMER    =   new ReentrantStopwatch("Rewrite with kompiled rules");
    public static final ReentrantStopwatch REWRITE_WITH_UNKOMPILED_RULES_TIMER  =   new ReentrantStopwatch("Rewrite with unkompiled rules");

    public static final ReentrantStopwatch PATTERN_MATCH_TIMER              =   new ReentrantStopwatch("Pattern match");
    public static final ReentrantStopwatch EVALUATE_SIDE_CONDITIONS_TIMER   =   new ReentrantStopwatch("Evaluate side conditions");
    public static final ReentrantStopwatch LOCAL_REWRITE_BUILD_RHS_TIMER    =   new ReentrantStopwatch("Build right-hand sides of local rewrites");

    public static final ReentrantStopwatch EVALUATE_LOOKUP_CHOICE_TIMER     =   new ReentrantStopwatch("Evaluate data-structure lookup & choice operations");
    public static final ReentrantStopwatch EVALUATE_REQUIRES_TIMER          =   new ReentrantStopwatch("Evaluate requires");

    public static final ReentrantStopwatch DEEP_CLONE_TIMER                 =   new ReentrantStopwatch("Deep clone");

    private static final Map<KLabelConstant, ReentrantStopwatch> FUNCTION_PROFILING_TIMERS = new HashMap<>();

    public static ReentrantStopwatch getTimerForFunction(KLabelConstant klabel) {
        if (enableProfilingMode.get()) {
            synchronized(FUNCTION_PROFILING_TIMERS) {
                ReentrantStopwatch stopwatch = FUNCTION_PROFILING_TIMERS.get(klabel);
                if (stopwatch == null) {
                   stopwatch = new ReentrantStopwatch(klabel.label());
                   FUNCTION_PROFILING_TIMERS.put(klabel, stopwatch);
                }
                return stopwatch;
            }
        } else {
            return null;
        }
    }

    public static void startTimer(ReentrantStopwatch timer) {
        if (enableProfilingMode.get()) {
            timer.start();
        }
    }

    public static void stopTimer(ReentrantStopwatch timer) {
        if (enableProfilingMode.get()) {
            timer.stop();
        }
    }

    public static void resetTimer(ReentrantStopwatch timer) {
        if (enableProfilingMode.get()) {
            timer.reset();
        }
    }

    public static void printResult() {
        if (enableProfilingMode.get()) {
            System.err.printf("%s = %s%n", EVALUATE_LOOKUP_CHOICE_TIMER.name, EVALUATE_LOOKUP_CHOICE_TIMER.toString());
            System.err.printf("%s = %s%n", EVALUATE_REQUIRES_TIMER.name, EVALUATE_REQUIRES_TIMER.toString());
            System.err.println("Top 10 most expensive functions:");
            SortedSet<ReentrantStopwatch> sorted = new TreeSet<>(new ReverseComparator<>());
            synchronized (FUNCTION_PROFILING_TIMERS) {
                sorted.addAll(FUNCTION_PROFILING_TIMERS.values());
            }
            Iterator<ReentrantStopwatch> iter = sorted.iterator();
            for (int i = 0; i < 10 && iter.hasNext(); i++) {
                ReentrantStopwatch stopwatch = iter.next();
                System.err.printf("%s = %s%n", stopwatch.name, stopwatch.toString());
            }
        }
    }

    private static class ReentrantStopwatch implements Comparable<ReentrantStopwatch> {

        private final String name;

        private final ThreadLocal<Stopwatch> stopwatch = new ThreadLocal<Stopwatch>() {
            @Override
            protected Stopwatch initialValue() {
                return Stopwatch.createUnstarted();
            }
        };

        private final ThreadLocal<Integer> count = new ThreadLocal<Integer>() {
            @Override
            protected Integer initialValue() {
                return 0;
            }
        };

        public ReentrantStopwatch(String name) {
            this.name = name;
        }

        public void start() {
            count.set(count.get() + 1);
            if (count.get() == 1) {
                stopwatch.get().start();
            }
        }

        public void stop() {
            count.set(count.get() - 1);
            if (count.get() == 0) {
                stopwatch.get().stop();
            } else if (count.get() < 0) {
                throw new AssertionError("Unable to stop timer: " + name + "\nTimer already stopped.");
            }
        }

        public void reset() {
            count.set(0);
            stopwatch.get().reset();
        }

        @Override
        public String toString() {
            return stopwatch.get().toString();
        }

        @Override
        public int compareTo(ReentrantStopwatch o) {
            return Long.compare(stopwatch.get().elapsed(TimeUnit.MICROSECONDS),
                    o.stopwatch.get().elapsed(TimeUnit.MICROSECONDS));
        }
    }

}

// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;

import com.google.common.base.Stopwatch;
import com.google.common.base.Ticker;

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

    public static final boolean ENABLE_PROFILING_MODE = true;

    public static final ReentrantStopwatch QUERY_RULE_INDEXING_TIMER            =   new ReentrantStopwatch("Query rule indexing");
    public static final ReentrantStopwatch REWRITE_WITH_KOMPILED_RULES_TIMER    =   new ReentrantStopwatch("Rewrite with kompiled rules");
    public static final ReentrantStopwatch REWRITE_WITH_UNKOMPILED_RULES_TIMER  =   new ReentrantStopwatch("Rewrite with unkompiled rules");

    public static final ReentrantStopwatch PATTERN_MATCH_TIMER              =   new ReentrantStopwatch("Pattern match");
    public static final ReentrantStopwatch EVALUATE_SIDE_CONDITIONS_TIMER   =   new ReentrantStopwatch("Evaluate side conditions");
    public static final ReentrantStopwatch LOCAL_REWRITE_BUILD_RHS_TIMER    =   new ReentrantStopwatch("Build right-hand sides of local rewrites");

    public static final ReentrantStopwatch EVALUATE_LOOKUP_CHOICE_TIMER     =   new ReentrantStopwatch("Evaluate data-structure lookup & choice operations");
    public static final ReentrantStopwatch EVALUATE_REQUIRES_TIMER          =   new ReentrantStopwatch("Evaluate requires");

    public static final ReentrantStopwatch DEEP_CLONE_TIMER                 =   new ReentrantStopwatch("Deep clone");

    public static void startTimer(ReentrantStopwatch timer) {
        if (ENABLE_PROFILING_MODE) {
            timer.start();
        }
    }

    public static void stopTimer(ReentrantStopwatch timer) {
        if (ENABLE_PROFILING_MODE) {
            timer.stop();
        }
    }

    public static void resetTimer(ReentrantStopwatch timer) {
        if (ENABLE_PROFILING_MODE) {
            timer.reset();
        }
    }

    public static void printResult() {
        if (ENABLE_PROFILING_MODE) {
            System.err.printf("%s(mc=%s, eval=%s[%s, %s], rew=%s) + %s%n",
                    REWRITE_WITH_KOMPILED_RULES_TIMER, PATTERN_MATCH_TIMER,
                    EVALUATE_SIDE_CONDITIONS_TIMER,
                    EVALUATE_LOOKUP_CHOICE_TIMER, EVALUATE_REQUIRES_TIMER,
                    LOCAL_REWRITE_BUILD_RHS_TIMER,
                    REWRITE_WITH_UNKOMPILED_RULES_TIMER);
            System.err.println(QUERY_RULE_INDEXING_TIMER);
            System.err.println(DEEP_CLONE_TIMER);
        }
    }

    private static class ReentrantStopwatch {

        private final String name;

        private final ThreadLocal<Stopwatch> stopwatch = new ThreadLocal<Stopwatch>() {
            @Override
            protected Stopwatch initialValue() {
                return Stopwatch.createUnstarted(new Ticker() {

                    ThreadMXBean bean = ManagementFactory.getThreadMXBean();

                    @Override
                    public long read() {
                        assert bean.isCurrentThreadCpuTimeSupported();
                        return bean.getCurrentThreadCpuTime();
                    }
                });
            }
        };

        private ThreadLocal<Integer> count = new ThreadLocal<Integer>() {
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
    }

}

// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Denis Bogdanas
 * Created on 26-Jul-18.
 */
public class Z3Profiler {
    private CounterStopwatch sw;
    private int requestCount;
    private int queryCount;
    private int queryBuildFailureCount;
    private int totalTimeouts;
    private int nonTimeouts;
    private boolean lastRunTimeout;
    private Map<String, Integer> queryResultCounts = new HashMap<>();

    Z3Profiler(String name) {
        sw = new CounterStopwatch(name + " time");
    }

    public void startRun() {
        sw.start();
    }

    public void endRun(int timeout) {
        long durationNano = sw.stopAndGetDuration();
        lastRunTimeout = (durationNano / 1000000.d) >= timeout;
        if (lastRunTimeout) {
            totalTimeouts++;
        } else {
            nonTimeouts++;
        }
    }

    public void queryResult(String result) {
        Integer cnt = queryResultCounts.get(result);
        cnt = cnt != null ? cnt : 0;
        queryResultCounts.put(result, cnt + 1);
    }

    /**
     * Not all requests result in actual SMT query. Some might have the results already cached.
     */
    public void newRequest() {
        requestCount++;
    }

    public void newQueryBuildFailure() {
        queryBuildFailureCount++;
    }

    public void startQuery() {
        queryCount++;
    }

    public boolean isLastRunTimeout() {
        return lastRunTimeout;
    }

    public void print() {
        if (queryCount == 0) {
            return;
        }
        int cachedQueries = requestCount - queryCount - queryBuildFailureCount;
        int unrecoveredTimeouts = queryCount - nonTimeouts;
        int recoveredTimeouts = totalTimeouts - unrecoveredTimeouts;
        Profiler2.printTimer("  ", sw, null, true);
        if (queryCount != 0) {
            if (queryCount != sw.getCountTop()) {
                System.err.format("    executed queries:     %d\n", queryCount);
            }
            for (String result : Z3Wrapper.Z3_QUERY_RESULTS) {
                if (queryResultCounts.get(result) != null) {
                    System.err.format("      %-14s:       %d\n", "unsat".equals(result) ? "unsat (proved)" : result,
                            queryResultCounts.get(result));
                }
            }
        }
        if (cachedQueries > 0) {
            System.err.format("    cached queries:       %d\n", cachedQueries);
        }
        if (queryBuildFailureCount > 0) {
            System.err.format("    query build failures: %d\n", queryBuildFailureCount);
        }
        if (unrecoveredTimeouts != 0) {
            System.err.format("    timeouts:             %d\n", unrecoveredTimeouts);
        }
        if (recoveredTimeouts != 0) {
            System.err.format("    recovered timeouts:   %d\n", recoveredTimeouts);
        }
    }
}

// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

/**
 * @author Denis Bogdanas
 * Created on 26-Jul-18.
 */
public class Z3Profiler {
    private CounterStopwatch sw;
    private int requestCount;
    private int queryCount;
    private int totalTimeouts;
    private int nonTimeouts;
    private boolean lastRunTimeout;

    Z3Profiler(String name) {
        sw = new CounterStopwatch(name);
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

    /**
     * Not all requests result in actual SMT query. Some might have the results already cached.
     */
    public void newRequest() {
        requestCount++;
    }

    public void startQuery() {
        queryCount++;
    }

    public boolean isLastRunTimeout() {
        return lastRunTimeout;
    }

    public int getQueryCount() {
        return queryCount;
    }

    public void print() {
        int cachedQueries = requestCount - queryCount;
        int unrecoveredTimeouts = queryCount - nonTimeouts;
        int recoveredTimeouts = totalTimeouts - unrecoveredTimeouts;
        System.err.format("  %s time:  %s\n", sw.getName(), sw);
        if (queryCount != 0) {
            System.err.format("    queries:            %d\n", queryCount);
        }
        if (cachedQueries > 0) {
            System.err.format("    cached queries:     %d\n", cachedQueries);
        }
        if (unrecoveredTimeouts != 0) {
            System.err.format("    timeouts:           %d\n", unrecoveredTimeouts);
        }
        if (recoveredTimeouts != 0) {
            System.err.format("    recovered timeouts: %d\n", recoveredTimeouts);
        }
    }
}

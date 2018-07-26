package org.kframework.backend.java.util;

/**
 * @author Denis Bogdanas
 * Created on 26-Jul-18.
 */
public class Z3Profiler {
    private CounterStopwatch sw;
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

    public void startQuery() {
        queryCount++;
    }

    public boolean isLastRunTimeout() {
        return lastRunTimeout;
    }

    public void print() {
        int unrecoveredTimeouts = queryCount - nonTimeouts;
        int recoveredTimeouts = totalTimeouts - unrecoveredTimeouts;
        System.err.format("  %s time:  %s\n", sw.getName(), sw);
        if (queryCount != 0) {
            System.err.format("    %s queries:   %d\n", sw.getName(), queryCount);
        }
        if (unrecoveredTimeouts != 0) {
            System.err.format("    %s timeouts:  %d\n", sw.getName(), unrecoveredTimeouts);
        }
        if (recoveredTimeouts != 0) {
            System.err.format("    %s recovered timeouts:    %d\n", sw.getName(), recoveredTimeouts);
        }
    }
}

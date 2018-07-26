package org.kframework.backend.java.util;

/**
 * A stopwatch that can be reentered recursively. Also counts the number of top-level invocations.
 * Time counted in nanoseconds, but displayed in ms.
 *
 * @author Denis Bogdanas
 * Created on 24-Jul-18.
 */
public class CounterStopwatch implements Comparable<CounterStopwatch> {

    private final String name;
    private long duration;
    private long lastStartNano;

    private int level = 0;
    private int count;

    CounterStopwatch(String name) {
        this.name = name;
    }

    public void start() {
        if (level == 0) {
            lastStartNano = System.nanoTime();
            count++;
        }
        level++;
    }

    /**
     * Should be called in a finally block to avoid exceptions leaving the level incremented.
     */
    public void stop() {
        level--;
        if (level == 0) {
            duration += (System.nanoTime() - lastStartNano);
        } else if (level < 0) {
            throw new AssertionError("Unable to stop timer: " + name + "\nTimer already stopped.");
        }
    }

    /**
     * If this call decreases counter to 0, stops the timer and returns the last duration. Otherwise returns 0.
     * <p>
     * Should be called in a finally block to avoid exceptions leaving the level incremented.
     */
    public long stopAndGetDuration() {
        level--;
        if (level == 0) {
            long lastDuration = System.nanoTime() - lastStartNano;
            this.duration += lastDuration;
            return lastDuration;
        } else if (level < 0) {
            throw new AssertionError("Unable to stop timer: " + name + "\nTimer already stopped.");
        }
        return 0;
    }

    public void reset() {
        level = 0;
        duration = 0;
    }

    @Override
    public String toString() {
        return String.format("%.3f s", (double) duration / 1000000000);
    }

    @Override
    public int compareTo(CounterStopwatch o) {
        return Long.compare(duration, o.duration);
    }

    public int getCount() {
        return count;
    }

    public int getLevel() {
        return level;
    }

    public String getName() {
        return name;
    }
}

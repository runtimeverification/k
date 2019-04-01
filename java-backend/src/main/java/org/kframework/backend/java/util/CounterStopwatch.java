// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.apache.commons.lang3.mutable.MutableInt;

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

    private final MutableInt level;
    private int countTop;
    private int countRecursive;

    public CounterStopwatch(String name) {
        this(name, new MutableInt());
    }

    /**
     * @param levelHolder Allows several Stopwatches share the same levelHolder, when they profile mutually recursive
     *                    functions.
     */
    public CounterStopwatch(String name, MutableInt levelHolder) {
        this.name = name;
        this.level = levelHolder;
    }

    public void start() {
        if (level.intValue() == 0) {
            lastStartNano = System.nanoTime();
            countTop++;
        } else {
            countRecursive++;
        }
        level.increment();
    }

    /**
     * Should be called in a finally block to avoid exceptions leaving the level incremented.
     */
    public void stop() {
        level.decrement();
        int level = this.level.intValue();
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
        level.decrement();
        int level = this.level.intValue();
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
        level.setValue(0);
        duration = 0;
    }

    @Override
    public String toString() {
        return String.format("%8.3f s", (double) duration / 1000000000);
    }

    @Override
    public int compareTo(CounterStopwatch o) {
        return Long.compare(duration, o.duration);
    }

    public int getCountTop() {
        return countTop;
    }

    public int getCountRecursive() {
        return countRecursive;
    }

    public int getLevel() {
        return level.intValue();
    }

    public MutableInt getSharedLevelHolder() {
        return level;
    }

    public String getName() {
        return name;
    }

    public CounterStopwatch minus(CounterStopwatch other) {
        CounterStopwatch result = new CounterStopwatch("");
        result.countTop = this.countTop - other.countTop;
        result.duration = this.duration - other.duration;
        return result;
    }
}

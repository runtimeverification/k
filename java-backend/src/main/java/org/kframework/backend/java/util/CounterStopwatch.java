// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.apache.commons.lang3.mutable.MutableInt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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
    private List<Counter> counters = new ArrayList<>();
    private List<CounterStopwatch> subTimers = new ArrayList<>();

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

    protected CounterStopwatch(String name, MutableInt level, long duration, int countTop, int countRecursive) {
        this.name = name;
        this.level = level;
        this.duration = duration;
        this.countTop = countTop;
        this.countRecursive = countRecursive;
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

    public long getDuration() {
        return duration;
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

    public Counter newCounter(String name) {
        Counter counter = new Counter(name, level);
        counters.add(counter);
        return counter;
    }

    private Counter leftoverCounter(String name) {
        return new Counter(name, level,
                countTop - counters.stream().mapToInt(Counter::getCountTop).sum(),
                countRecursive - counters.stream().mapToInt(Counter::getCountRecursive).sum());
    }

    public List<Counter> getCounters(String leftoverCounterName) {
        if (counters.isEmpty()) {
            return Collections.emptyList();
        }
        List<Counter> result = new ArrayList<>(counters);
        result.add(leftoverCounter(leftoverCounterName));
        return result;
    }

    public CounterStopwatch newSubTimer(String name, MutableInt levelHolder) {
        CounterStopwatch subTimer = new CounterStopwatch(name, levelHolder);
        subTimers.add(subTimer);
        return subTimer;
    }

    public CounterStopwatch newSubTimer(String name) {
        return newSubTimer(name, new MutableInt());
    }

    private CounterStopwatch leftoverTimer(String name) {
        return new CounterStopwatch(name, new MutableInt(),
                duration - subTimers.stream().mapToLong(CounterStopwatch::getDuration).sum(),
                countTop - subTimers.stream().mapToInt(CounterStopwatch::getCountTop).sum(),
                countRecursive - subTimers.stream().mapToInt(CounterStopwatch::getCountRecursive).sum());
    }

    public List<CounterStopwatch> getSubTimers(String leftoverTimerName) {
        if (subTimers.isEmpty()) {
            return Collections.emptyList();
        }
        List<CounterStopwatch> result = new ArrayList<>(subTimers);
        result.add(leftoverTimer(leftoverTimerName));
        return result;
    }
}

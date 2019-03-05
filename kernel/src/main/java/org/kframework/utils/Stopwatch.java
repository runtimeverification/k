// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils;

import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;

import com.google.inject.Inject;
import java.util.Formatter;

/**
 * To use, access {@link #instance()} after calling {@link #init(GlobalOptions) init()}.
 */
@RequestScoped
public class Stopwatch {
    private long start;
    private long lastIntermediate;
    Formatter f = new Formatter(System.out);
    private final GlobalOptions options;

    @Inject
    public Stopwatch(GlobalOptions options) {
        this.options = options;
        start = System.currentTimeMillis();
        lastIntermediate = start;
    }

    public void start() {
        printIntermediate("Init");
    }

    public void printIntermediate(String message) {
        long current = System.currentTimeMillis();
        if (options.verbose)
            f.format("%-60s = %s%n", message, milisecondsToTime(lastIntermediate - start));
        lastIntermediate = current;
    }

    public void printTotal(String message) {
        printIntermediate("Cleanup");
        if (options.verbose)
            f.format("%-60s = %s%n", message, milisecondsToTime(lastIntermediate - start));
    }

    private static String milisecondsToTime(long miliseconds) {
        long h = miliseconds / 3600000;
        long m = miliseconds % 3600000 / 60000;
        double s = miliseconds % 60000 / 1000.;
        if (h > 0)
            return String.format("%dh %02dm %02ds", h, m, (long) s);
        if (m > 0)
            return String.format("%dm %02ds", m, (long) s);
        return String.format("%6.3fs", s);
    }

    public long getIntermediateMilliseconds() {
        long endd = System.currentTimeMillis();
        long rez = lastIntermediate - endd;
        lastIntermediate = endd;
        return rez;
    }
}

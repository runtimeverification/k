// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import org.kframework.main.GlobalOptions;

import java.util.Formatter;

/**
 * To use, access {@link #instance()} after calling {@link #init(GlobalOptions) init()}.
 */
public class Stopwatch {
    private static Stopwatch sw;
    private long start;
    private long lastIntermediate;
    Formatter f = new Formatter(System.out);
    private GlobalOptions options;

    /**
     * Must be called before attempting to call 
     * {@link #printIntermediate(String) printIntermediate} or {@link #printTotal(String) printTotal}.
     * @param options a {@link GlobalOptions} instance instantiated with the correct value of the 
     * {@link GlobalOptions#verbose verbose} field.
     */
    public void init(GlobalOptions options) {
        this.options = options;
    }
    
    public static Stopwatch instance() {
        if (sw == null) {
            sw = new Stopwatch();
        }
        return sw;
    }

    /**
     * This is a singleton.
     */
    private Stopwatch() {
        start = System.currentTimeMillis();
        lastIntermediate = start;
    }

    public void start() {
        printIntermediate("Init");
    }

    public void printIntermediate(String message) {
        assert options != null;
        long current = System.currentTimeMillis();
        if (options.verbose)
            f.format("%-60s = %5d%n", message, current - lastIntermediate);
        lastIntermediate = current;
    }

    public void printTotal(String message) {
        assert options != null;
        printIntermediate("Cleanup");
        if (options.verbose)
            f.format("%-60s = %5d%n", message, lastIntermediate - start);
    }

    public long getIntermediateMilliseconds() {
        long endd = System.currentTimeMillis();
        long rez = lastIntermediate - endd;
        lastIntermediate = endd;
        return rez;
    }
}

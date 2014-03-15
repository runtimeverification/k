package org.kframework.utils;

import org.kframework.main.GlobalOptions;

import java.util.Formatter;

public class Stopwatch {
    private static Stopwatch sw;
    private long start;
    private long lastIntermediate;
    Formatter f = new Formatter(System.out);
    private GlobalOptions options;

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

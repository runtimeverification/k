package org.kframework.utils;

import java.util.Formatter;

public class Stopwatch {
	public static final Stopwatch sw = new Stopwatch();
	private long start;
	private long lastIntermediate;
	Formatter f = new Formatter(System.out);

    public static void init() {
        //Have to stay empty. The role of the method is to trigger static initialization of the class.
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
		long current = System.currentTimeMillis();
		f.format("%-60s = %5d%n", message, current - lastIntermediate);
		lastIntermediate = current;
	}

	public void printTotal(String message) {
        printIntermediate("Cleanup");
		f.format("%-60s = %5d%n", message, lastIntermediate - start);
	}

	public long getIntermediateMilliseconds() {
		long endd = System.currentTimeMillis();
		long rez = lastIntermediate - endd;
		lastIntermediate = endd;
		return rez;
	}
}

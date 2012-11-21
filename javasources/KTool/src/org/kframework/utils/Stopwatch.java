package org.kframework.utils;

import java.util.Formatter;

public class Stopwatch {
	private long start = 0;
	private long start2 = 0;
	Formatter f = new Formatter(System.out);

	public Stopwatch() {
		start = System.currentTimeMillis();
		start2 = start;
	}

	public void Start() {
		start = System.currentTimeMillis();
		start2 = start;
	}

	public void printIntermediate(String message) {
		long endd = System.currentTimeMillis();
		f.format("%-60s = %5d%n", message, endd - start2);
		start2 = endd;
	}

	public void printTotal(String message) {
		long endd = System.currentTimeMillis();
		f.format("%-60s = %5d%n", message, endd - start);
	}
}

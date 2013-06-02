package org.kframework.parser.utils;

public class SglrJNI {
	static {
		System.loadLibrary("SglrJNI"); // hello.dll (Windows) or libhello.so (Unixes)
		init();
	}

	// A native method that receives nothing and returns void
	private static native void init();

	/**
	 * The main parsing function that accesses the C parser in native way.
	 * The library is loaded only once and it is persistent.
	 * @param parseTablePath - the path to the parse table. Note that it will be cached.
	 * @param input - the string to parse
	 * @param startSymbol - the start sort
	 * @param inputFileName - this is required to annotate the nodes with location information. It can be any string.
	 * @return a byte array in containing the ATerm in the BAF format.
	 */
	public static native byte[] parse(String parseTablePath, String input, String startSymbol, String inputFileName);
}

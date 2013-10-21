package org.kframework.parser.utils;

public class SglrJNI {
	/**
	 * The main parsing function that accesses the C parser in native way.
	 * The library is loaded only once and it is persistent.
	 * @param parseTablePath - the path to the parse table. Note that it will be cached.
	 * @param input - the string to parse
	 * @param startSymbol - the start sort
	 * @param inputFileName - this is required to annotate the nodes with location information. It can be any string.
	 * @return a byte array in containing the ATerm in the BAF format.
	 */
	public static byte[] parseString(String parseTablePath, String input, String startSymbol, String inputFileName) {
		if (firstTime) {
			System.loadLibrary("SglrJNI");
			init();
			firstTime = false;
		}
		return parse(parseTablePath, input, startSymbol, inputFileName);
	}

	// A flag signaling whether this is the first time the parser is instantiated.
	private static boolean firstTime = true;

	// A native parser initialization method that receives nothing and returns void.  It must be called only once.
	private static native void init();

	// A delegate native method that parses the string into a BAF array.
	private static native byte[] parse(String parseTablePath, String input, String startSymbol, String inputFileName);
}

package org.kframework.parser.utils;

import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

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
			String arch = System.getProperty("os.arch");
			if (GlobalSettings.isWindowsOS()) {
				if (arch.toLowerCase().contains("64")) {
					System.load(KPaths.getKBase(false) + "/lib/native/cygwin/x64/SglrJNI.dll");
				} else
					System.load(KPaths.getKBase(false) + "/lib/native/cygwin/SglrJNI.dll");
			} else if (GlobalSettings.isUnixOS()) {
				if (arch.toLowerCase().contains("64")) {
					System.load(KPaths.getKBase(false) + "/lib/native/linux/x64/libSglrJNI.so");
				} else
					System.load(KPaths.getKBase(false) + "/lib/native/linux/libSglrJNI.so");
			} else if (GlobalSettings.isMacOS())
				System.load(KPaths.getKBase(false) + "/lib/native/macosx/libSglrJNI.jnilib");
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

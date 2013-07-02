package org.kframework.parser.utils;

import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class SglrJNI {
    static {
//		System.loadLibrary("SglrJNI"); // hello.dll (Windows) or libhello.so (Unixes)

        System.load(getSglriLibraryPath());

        init();
    }

    private static String getSglriLibraryPath() {
        String path = KPaths.getKBase(false) + "/lib/native";

        if (GlobalSettings.isUnixOS()) {
            String arch = System.getProperty("os.arch");
            if (arch.toLowerCase().contains("64")) {
                path += "/linux/x64/libSglrJNI.so";
            } else {
                path += "/linux/libSglrJNI.so";
            }
        }
        if (GlobalSettings.isWindowsOS()) {
        	path += "/cygwin/SglrJNI.dll";
        }
        if (GlobalSettings.isMacOS()) {
			path += "/macosx/libSglrJNI.jnilib";
        }
        return path;
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

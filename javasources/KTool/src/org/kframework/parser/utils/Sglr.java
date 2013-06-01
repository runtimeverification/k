package org.kframework.parser.utils;

import java.io.ByteArrayInputStream;
import java.io.IOException;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.JavaClassesFactory;

import aterm.ATerm;
import aterm.pure.PureFactory;
import aterm.pure.binary.BAFReader;

public class Sglr {

	public static ASTNode run_sglri(String tablePath, String startSymbol, String content) {
		byte[] parsed = SglrJNI.parse(tablePath, content, startSymbol, "rule");
		try {
			ByteArrayInputStream inputStream = new ByteArrayInputStream(parsed);
			inputStream.read(); // the BAF format starts with a 0 that has to go away first.
			ATerm aterm = new BAFReader(new PureFactory(), inputStream).readFromBinaryFile(false);

			return JavaClassesFactory.getTerm(aterm);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}

	private static boolean isUnixOS() {
		String os = System.getProperty("os.name").toLowerCase();
		return os.contains("nix") || os.contains("nux");
	}

	private static boolean isWindowsOS() {
		return System.getProperty("os.name").toLowerCase().contains("win");
	}

	private static boolean isMacOS() {
		return System.getProperty("os.name").toLowerCase().contains("mac");
	}
}

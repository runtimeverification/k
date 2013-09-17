package org.kframework.parser.utils;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.JavaClassesFactory;

import aterm.ATerm;
import aterm.pure.PureFactory;
import aterm.pure.binary.BAFReader;

public class Sglr {
	private static final boolean useJNI = false;
	private static final boolean useSRV = true;

	/**
	 * The main parsing function that accesses the C parser in native way.
	 * The library is loaded only once and it is persistent.
	 * @param tablePath - the path to the parse table. Note that it will be cached.
	 * @param input - the string to parse
	 * @param startSymbol - the start sort
	 * @param location - this is required to annotate the nodes with location information. It can be any string.
	 * @return the ASTNode corresponding to the DAG parse forest returned by the parser.
	 */
	@SuppressWarnings({ "unused" })
	public static ASTNode run_sglri(String tablePath, String startSymbol, String input, String location) {
		tablePath = new File(tablePath).getAbsolutePath();
		// should parse both ways and compare, but JNI way is broken on 64 bits.
		byte[] parsed = null;
		if (useJNI) {
			parsed = SglrJNI.parseString(tablePath, input, startSymbol, location);
		}
		byte[] served = null;
		if (useSRV) {
			served = SglrServer.parseString(tablePath, input, startSymbol, location);
		}
		if (useJNI && useSRV) {
			if (!Arrays.equals(parsed, served)) {
				try {
					ATerm jniTerm = parseATerm(parsed);
					ATerm srvTerm = parseATerm(served);
					ByteArrayOutputStream jniStream = new ByteArrayOutputStream();
					jniTerm.writeToSharedTextFile(jniStream);
					ByteArrayOutputStream srvStream = new ByteArrayOutputStream();
					srvTerm.writeToSharedTextFile(srvStream);
					if (!Arrays.equals(jniStream.toByteArray(), srvStream.toByteArray())) {
						System.err.println("Error, different results from sglr through jni and server");
						System.err.println(parsed.length + " bytes from JNI, " + served.length + " bytes from server");
						System.exit(1);
					} else {
						System.err.println("Different but equivalent results from jni and server parsing input from " + location);
						System.err.println(input);
						System.err.println("Against nonterminal " + startSymbol + " in grammar " + tablePath);
						System.err.println("Result lengths " + parsed.length + ", " + served.length);
					}
				} catch (IOException e) {
					e.printStackTrace();
					System.exit(1);
				}
			}
		}
		if (useSRV && !useJNI) {
			parsed = served;
		}
		try {
			ATerm aterm = parseATerm(parsed);
			JavaClassesFactory.clearCache();

			return JavaClassesFactory.getTerm(aterm);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}

	private static ATerm parseATerm(byte[] parsed) throws IOException {
		ByteArrayInputStream inputStream = new ByteArrayInputStream(parsed);
		inputStream.read(); // the BAF format starts with a 0 that has to go away first.
		ATerm aterm = new BAFReader(new PureFactory(), inputStream).readFromBinaryFile(false);
		return aterm;
	}
}

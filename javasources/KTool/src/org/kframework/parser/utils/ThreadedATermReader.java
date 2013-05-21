package org.kframework.parser.utils;

import java.io.IOException;
import java.io.InputStream;

import aterm.ATerm;
import aterm.ParseError;
import aterm.pure.PureFactory;
import aterm.pure.binary.BAFReader;

public class ThreadedATermReader extends Thread {

	InputStream inputStream;
	ATerm aterm;

	public ThreadedATermReader(InputStream inputStream) {
		this.inputStream = inputStream;
	}

	public void run() {
		try {
			inputStream.read(); // the BAF format starts with a 0 that has to go away first.
			aterm = new BAFReader(new PureFactory(), inputStream).readFromBinaryFile(false);
		} catch (ParseError e1) {
			e1.printStackTrace();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}

	public ATerm getAterm() {
		return aterm;
	}
}

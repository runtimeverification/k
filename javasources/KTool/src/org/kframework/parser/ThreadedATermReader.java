package org.kframework.parser;

import java.io.BufferedInputStream;
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
		this.inputStream = (InputStream) new BufferedInputStream(inputStream);
	}

	public void run() {
		try {
			System.out.println(inputStream.read()); // the BAF format starts with a '!' that has to go away first.
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

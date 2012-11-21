package org.kframework.krun.ioserver.resources;

import javax.imageio.IIOException;
import java.io.*;
import java.net.URI;

public class ResourceOutFile extends FileResource {

	
	private OutputStream of;
	
	public ResourceOutFile(URI uri, String args) throws FileNotFoundException {
		boolean append = false;
		if (args.contains("a"))
			append = true;
		File file = new File(uri);
		of = new FileOutputStream(file, append);
	}

	
	public ResourceOutFile(PrintStream out) {
		of = out;
	}


	@Override
	public void close() throws Exception {
		of.close();
	}

	@Override
	public void flush() throws Exception {
		of.flush();
	}

	@Override
	public Byte peek() throws Exception {
		throw new IIOException("Cannot peek into a write-only file.");
	}

	@Override
	public Byte readbyte() throws Exception {
		throw new IIOException("Cannot read from a write-only file.");
	}

	@Override
	public void seek(int position) throws Exception {
		throw new IIOException("Seek not implemented.");
	}

	@Override
	public void writebyte(byte bite) throws Exception {
		of.write(bite);
	}

	@Override
	public void writebytes(byte[] bite) throws Exception {
		of.write(bite);
	}

	@Override
	public Long position() throws Exception {
		throw new IIOException("Position not implemented.");
	}


	@Override
	public Byte eof() throws Exception {
		throw new IIOException("Eof not implemented.");
	}


	@Override
	public void sendToInput(String s) throws Exception {
		throw new Exception("Not applicable for streams.");
	}


	@Override
	public String getFromOutput() throws Exception {
		throw new Exception("Not applicable for streams.");
	}

}

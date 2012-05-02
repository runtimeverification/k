package resources;

import java.io.EOFException;
import java.io.InputStream;

import javax.imageio.IIOException;

public class BufferedReader extends Resource{

	private InputStream is;
	private int integer;
	
	public BufferedReader(InputStream is) {
		this.is = is;
		integer = -2;
	}

	@Override
	public void close() throws Exception {
		is.close();
	}

	@Override
	public Byte eof() throws Exception {
		return integer == -1 ? (byte) 1 : 0;
	}

	@Override
	public void flush() throws Exception {
//		throw new IIOException("Peek not implemented for input streams");
	}

	@Override
	public Byte peek() throws Exception {
		if (integer==-2&&is.available()>0) {
			integer = is.read();
		}
		if (eof() == 1)
			throw new EOFException("EOF");
		return (byte) integer;
	}

	@Override
	public Long position() throws Exception {
		throw new IIOException("Position not implemented for input streams");
	}

	@Override
	public Byte readbyte() throws Exception {
		int tmp;
		if (integer == -2) {
			tmp = is.read();
			if (tmp == -1) throw new EOFException();
		} else {
			tmp = integer;
			integer=-2;
		}
		integer = peek();
		return (byte)tmp;
	}

	@Override
	public void seek(int position) throws Exception {
		throw new IIOException("Seek not implemented for input streams");
	}

	@Override
	public void writebyte(byte ascii) throws Exception {
		throw new IIOException("Writebyte not implemented for input streams");
	}

}

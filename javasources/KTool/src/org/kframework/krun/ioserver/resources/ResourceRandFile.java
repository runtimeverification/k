package org.kframework.krun.ioserver.resources;

import java.io.EOFException;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.RandomAccessFile;
import java.net.URI;
import java.util.Arrays;
/**
 * This Resource is an ordinary file.
 * @author andrei.arusoaie
 *
 */
public class ResourceRandFile extends FileResource {

	private URI uri;
	private RandomAccessFile raf;

	public ResourceRandFile(URI uri, String args) throws FileNotFoundException {
		this.uri = uri;
		File file = new File(uri);
		raf = new RandomAccessFile(file, args);
	}

	@Override
	public void close() throws Exception {
		raf.close();
	}

	@Override
	public void flush() throws Exception {
		raf.getFD().sync();
	}

	@Override
	public Byte peek() throws Exception {
		Byte ascii = raf.readByte();
		raf.seek(-1);
		return ascii;
	}

	@Override
	public Byte readbyte() throws Exception {
		return raf.readByte();
	}

	@Override
	public byte[] readbytes(int numBytes) throws Exception {
		byte[] result = new byte[numBytes];
		int tmp = raf.read(result, 0, numBytes);
		if (tmp == -1) throw new EOFException();
		return Arrays.copyOfRange(result, 0, tmp);
	}

	@Override
	public void seek(int position) throws Exception {
		raf.seek(position);
	}

	@Override
	public void writebyte(byte bite) throws Exception {
		raf.writeByte(bite);
	}

	@Override
	public void writebytes(byte[] bite) throws Exception {
		raf.write(bite);
	}

	@Override
	public Long position() throws Exception {
		return raf.getFilePointer();
	}

	public URI getUri() {
		return uri;
	}

	@Override
	public Byte eof() throws Exception {
		return raf.getFilePointer() == raf.length() ? (byte) 1 : 0;
	}

	@Override
	public void sendToInput(String s) throws Exception {
		// TODO Auto-generated method stub
		
	}

	@Override
	public String getFromOutput() throws Exception {
		// TODO Auto-generated method stub
		return null;
	}
}

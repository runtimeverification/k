package resources;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URI;

import javax.imageio.IIOException;

public class ResourceOutFile extends Resource {

	
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
	public Long position() throws Exception {
		throw new IIOException("Position not implemented.");
	}


	@Override
	public Byte eof() throws Exception {
		throw new IIOException("Eof not implemented.");
	}

}

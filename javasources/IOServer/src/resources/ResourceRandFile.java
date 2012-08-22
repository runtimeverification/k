package resources;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.RandomAccessFile;
import java.net.URI;
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
	public void seek(int position) throws Exception {
		raf.seek(position);
	}

	@Override
	public void writebyte(byte bite) throws Exception {
		raf.writeByte(bite);
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

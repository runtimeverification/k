package resources;


public class ResourceInFile extends FileResource {

	static BufferedReader in = new BufferedReader(System.in);
	String uri;
	

	@Override
	public void close() throws Exception {
		in.close();
	}

	@Override
	public void flush() throws Exception {
		in.flush();
	}

	@Override
	public Byte peek() throws Exception {
		return in.peek();
	}

	@Override
	public Byte readbyte() throws Exception {
		return in.readbyte();
	}

	@Override
	public void seek(int position) throws Exception {
		in.seek(position);
	}

	@Override
	public void writebyte(byte bite) throws Exception {
		in.writebyte(bite);
	}

	@Override
	public Long position() throws Exception {
		return in.position();
	}

	@Override
	public Byte eof() throws Exception {
		return in.eof();
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

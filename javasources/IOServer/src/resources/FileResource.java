package resources;

/**
 * Generic class for all types of resources.
 * It specifies all the methods which have to be implemented by each Resource.
 * @author andrei.arusoaie
 *
 */
public abstract class FileResource extends Resource {

	public abstract void flush() throws Exception;
	public abstract Byte peek() throws Exception;
	public abstract Byte readbyte() throws Exception;
	public abstract void seek(int position) throws Exception;
	public abstract void writebyte(byte ascii) throws Exception;
	public abstract Long position() throws Exception;
	public abstract Byte eof() throws Exception;
}

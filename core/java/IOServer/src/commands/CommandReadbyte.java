package commands;

import java.io.EOFException;
import java.net.Socket;

import resources.Resource;
import resources.ResourceSystem;

public class CommandReadbyte extends Command {


	private long ID;

	public CommandReadbyte(String[] args, Socket socket) { //, Long maudeId) {
		super(args, socket); //, maudeId);

		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("read byte operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {
		// retrieve file struct
		Resource resource = ResourceSystem.getResource(ID);

		// call corresponding method on file
		Byte ascii = null;
		try {
			ascii = resource.readbyte();

			// success
			succeed(new String[] { ascii.toString() });
		}
		catch (EOFException eof)
		{
			fail("EOF");
		}
		catch (Exception e) {
			fail("Cannot read byte from resource " + ID);
		}

	}

}

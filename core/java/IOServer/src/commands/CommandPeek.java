package commands;

import java.io.EOFException;
import java.net.Socket;

import resources.Resource;
import resources.ResourceSystem;

public class CommandPeek extends Command {

	
	
	private long ID;

	public CommandPeek(String[] args, Socket socket) { //, Long maudeId) {
		super(args, socket); //, maudeId);

		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("peek operation aborted: " + nfe.getLocalizedMessage());
		}

	}

	public void run() {

		// retrieve file struct
		Resource resource = ResourceSystem.getResource(ID);
		
		try {
			Byte peek = resource.peek();
			if (peek != null)
				succeed(new String[] { peek.toString() });
			else
				fail("peek: cannot peek from resource " + ID);
		} catch (EOFException eof) {
			fail("EOF");
		}catch (Exception e) {
			e.printStackTrace();
		}
	}

}

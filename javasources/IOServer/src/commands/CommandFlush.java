package commands;

import java.net.Socket;
import java.util.logging.Logger;
import resources.FileResource;
import resources.ResourceSystem;


public class CommandFlush extends Command {

	private long ID;

	public CommandFlush(String[] args, Socket socket, Logger logger) { //, Long maudeId) {
		super(args, socket, logger); //, maudeId);
		
		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("flush operation aborted: " + nfe.getLocalizedMessage());
		}

	}

	public void run() {
		// retrieve file struct
		FileResource resource = (FileResource)ResourceSystem.getResource(ID);

		// call corresponding method on file
		try {
			resource.flush();

			// success
			succeed(new String[] { "success" });

		} catch (Exception e) {
			// TODO Auto-generated catch block
			fail("Cannot flush resource " + ID);
			e.printStackTrace();
		}
	}

}

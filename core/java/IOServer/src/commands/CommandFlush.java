package commands;

import java.net.Socket;

import resources.Resource;
import resources.ResourceSystem;


public class CommandFlush extends Command {

	private long ID;

	public CommandFlush(String[] args, Socket socket) { //, Long maudeId) {
		super(args, socket); //, maudeId);
		
		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("flush operation aborted: " + nfe.getLocalizedMessage());
		}

	}

	public void run() {
		// retrieve file struct
		Resource resource = ResourceSystem.getResource(ID);

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

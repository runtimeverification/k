package commands;

import java.net.Socket;
import java.util.logging.Logger;
import resources.Resource;
import resources.ResourceSystem;

public class CommandPosition extends Command {


	private long ID;

	public CommandPosition(String[] args, Socket socket, Logger logger) { //, Long maudeId) {
		super(args, socket, logger); //, maudeId);

		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("position operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {
		// retrieve file struct
		Resource resource = ResourceSystem.getResource(ID);

		// call corresponding method on file
		try {
			Long position = resource.position();

			// success
			succeed(new String[] { position.toString() });

		} catch (Exception e) {
			// TODO Auto-generated catch block
			fail("Cannot get position in resource " + ID);
			e.printStackTrace();
		}
	}

}

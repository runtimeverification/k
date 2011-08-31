package commands;

import java.net.Socket;

import resources.ResourceSystem;

public class CommandReopen extends Command {

	private String uri;
	private long ID;
	private String[] args;
	
	public CommandReopen(String[] args, Socket socket) { //, Long maudeId) {
		super(args, socket); //, maudeId);

		this.args = args;
		this.uri = args[2];
		
		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("reopen operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {
		try {
			// retrieve file struct
			Long ID = ResourceSystem.getNewResource(this.ID, uri, args);

			if (ID != null)
				succeed(new String[] { ID.toString() });
			else
				fail("open: cannot open/create resource " + uri);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}

package commands;

import java.net.Socket;

import resources.ResourceSystem;


public class CommandOpen extends Command {

	private String uri;
	private String[] args;
	
	public CommandOpen(String[] args, Socket socket) { //, Long maudeId) {
		super(args, socket); //, maudeId);

		// uri#attribute1=v1#a2=v2...
		uri = args[1];
		this.args = args;
	}

	public void run() {

		try {
			Long ID = ResourceSystem.getNewResource(uri, args);

			if (ID != null)
				succeed(new String[] { ID.toString() });
			else
				fail("open: cannot open/create resource " + uri);
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

}

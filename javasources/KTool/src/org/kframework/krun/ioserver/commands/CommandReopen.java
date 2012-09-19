package org.kframework.krun.ioserver.commands;

import java.net.Socket;

import java.util.logging.Logger;

import org.kframework.krun.ioserver.resources.ResourceSystem;

public class CommandReopen extends Command {

	private String uri;
	private long ID;
	private String[] args;
	
	public CommandReopen(String[] args, Socket socket, Logger logger) { //, Long maudeId) {
		super(args, socket, logger); //, maudeId);

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

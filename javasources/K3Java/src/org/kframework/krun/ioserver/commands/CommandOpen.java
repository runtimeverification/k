package org.kframework.krun.ioserver.commands;

import java.net.Socket;
import java.util.logging.Logger;

import org.kframework.krun.ioserver.resources.ResourceSystem;


public class CommandOpen extends Command {

	private String uri;
	private String[] args;
	
	public CommandOpen(String[] args, Socket socket, Logger logger) { //, Long maudeId) {
		super(args, socket, logger); //, maudeId);

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

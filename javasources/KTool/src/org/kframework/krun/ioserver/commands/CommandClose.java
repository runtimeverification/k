package org.kframework.krun.ioserver.commands;

import org.kframework.krun.ioserver.resources.Resource;
import org.kframework.krun.ioserver.resources.ResourceSystem;

import java.net.Socket;
import java.util.logging.Logger;



public class CommandClose extends Command {

	private Long ID;

	public CommandClose(String[] args, Socket socket, Logger logger) { //, Long maudeId) {

		// the form of the request should be: close#ID
		super(args, socket, logger); //, maudeId);

		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("close operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {

		// retrieve file struct
		Resource resource = ResourceSystem.getResource(ID);
		if (resource == null) {
			fail("EBADF");
			return;
		}

		// call corresponding method on resource
		try {
			resource.close();

			ResourceSystem.remove(ID);
			
			// success
			succeed(new String[] { "success" });
		} catch (Exception e) {
			// TODO Auto-generated catch block
			fail("Cannot close resource " + ID);
			e.printStackTrace();
		}

	}

}

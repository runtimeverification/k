package org.kframework.krun.ioserver.commands;

import org.kframework.krun.ioserver.resources.FileResource;
import org.kframework.krun.ioserver.resources.ResourceSystem;

import java.net.Socket;
import java.util.logging.Logger;

public class CommandWritebytes extends Command {


	private long ID;
	private String string;
	private byte[] bytes;

	public CommandWritebytes(String[] args, Socket socket, Logger logger) { //, Long maudeId) {
		super(args, socket, logger); //, maudeId);

		try {
			ID = Long.parseLong(args[1]);
			// ascii = Byte.parseByte(args[2]);
			string = "";
			String conn = "";
			for (int i = 2; i < args.length - 3; i++) {
				string += conn + args[i];
				conn = "\001";
			}
			bytes = string.getBytes();
		} catch (NumberFormatException nfe) {
			fail("write operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {
		
		// get resource
		FileResource resource = (FileResource)ResourceSystem.getResource(ID);
		
		try {
			resource.writebytes(bytes);
			succeed(new String[] { "success" });
		} catch (Exception e) {
			fail("seek: cannot write " + string + " in resource " + ID);
		}
	}

}

package org.kframework.krun.ioserver.commands;

import org.kframework.krun.ioserver.resources.FileResource;
import org.kframework.krun.ioserver.resources.ResourceSystem;

import java.io.EOFException;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandReadbytes extends Command {

	private long ID;
	private int numBytes;

	public CommandReadbytes(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);

		try {
			ID = Long.parseLong(args[1]);
			numBytes = Integer.parseInt(args[2]);
		} catch (NumberFormatException nfe) {
			fail("read bytes operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {
		FileResource resource = (FileResource) ResourceSystem.getResource(ID);

		byte[] bytes = null;
		try {
			bytes = resource.readbytes(numBytes);
			succeed(new String[] { new String(bytes) });
		} catch (EOFException eof) {
			fail("EOF");
		} catch (Exception e) {
			fail("Cannot read bytes from resource " + ID);
		}
	}
}

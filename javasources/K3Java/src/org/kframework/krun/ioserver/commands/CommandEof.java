package org.kframework.krun.ioserver.commands;

import java.net.Socket;
import java.util.logging.Logger;

import org.kframework.krun.ioserver.resources.FileResource;
import org.kframework.krun.ioserver.resources.ResourceSystem;

public class CommandEof extends Command {

	private long ID;

	public CommandEof(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);

		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("eof operation aborted: " + nfe.getLocalizedMessage());
		}
}

	public void run() {
		try{
			FileResource resource = (FileResource)ResourceSystem.getResource(ID);
			Byte bite = resource.eof();
			succeed(new String[] { bite.toString() });
		}
		catch (Exception e)
		{
			fail(e.getLocalizedMessage());
		}
	}

}

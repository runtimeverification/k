package org.kframework.krun.ioserver.commands;

import java.io.File;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandMTime extends Command {
	private String path;

	public CommandMTime(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);
		path = args[1];
	}

	public void run() {
		try {
			File f = new File(path);
			succeed(new String[] { Long.toString(f.lastModified()) });
		} catch (Exception e) {
			fail(e.getLocalizedMessage());
		}
	}
}

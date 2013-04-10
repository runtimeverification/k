package org.kframework.krun.ioserver.commands;

import java.io.File;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandIsFile extends Command {

	private String path;

	public CommandIsFile(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);

		path = args[1];
	}

	public void run() {
		try {
			File f = new File(path);
			if (f.isFile()) {
				succeed(new String[] { "1" });
			} else {
				succeed(new String[] { "0" });
			}
		} catch (Exception e) {
			fail(e.getLocalizedMessage());
		}
	}
}

package main;

import log.Logger;
import resources.ResourceSystem;

public class Main {
	
	public static void main(String[] args) throws Exception {
		
		// Initialize resource system
		Long r;
		r = ResourceSystem.getNewResource("stdin:///", null);
		assert(r == 0);
		
		r = ResourceSystem.getNewResource("stdout:///", null);
		assert(r == 1);
		
		r = ResourceSystem.getNewResource("stderr:///", null);
		assert(r == 2);

		IOServer server = null;
		try {
			int port = Integer.parseInt(args[0]);
			server = new IOServer(port);
		} catch (NumberFormatException e) {
			Logger.warning("An error occurred when initializing port. Server will use the default port.");
			server = new IOServer(8989);
		}
		
		server.acceptConnections();
	}
}

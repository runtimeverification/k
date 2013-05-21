package org.kframework.krun.ioserver.main;

import org.kframework.kil.loader.Context;
import org.kframework.krun.ioserver.resources.ResourceSystem;

import java.util.logging.Logger;

public class MainServer implements Runnable {
	public int _port;
	public boolean _started;
	private Logger _logger;
	protected Context context;

	public MainServer(int port, Logger logger, Context context) {
		this.context = context;
		_port = port;
		_logger = logger;
		try {
			createDefaultResources();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	public void run() {
		IOServer server = new IOServer(_port, _logger, context);
		_port = server.port; // in case server changes port
		_started = true;
		try {
			server.acceptConnections();
		} catch (java.io.IOException e) {
			_logger.severe("Error accepting connection:" + e);
		}
	}

	private void createDefaultResources() throws Exception {
		// Initialize resource system
		Long r;
		r = ResourceSystem.getNewResource("stdin:/", null);
		assert(r == 0);
		
		r = ResourceSystem.getNewResource("stdout:/", null);
		assert(r == 1);
		
		r = ResourceSystem.getNewResource("stderr:/", null);
		assert(r == 2);
	}
		
	public static void main(String[] args) throws Exception {
		Context context = new Context();
		Logger logger = java.util.logging.Logger.getLogger("KRunner");
		logger.setUseParentHandlers(false);
		MainServer ms = new MainServer(Integer.parseInt(args[0]), logger, context);
		
		ms.run();
		//start(Integer.parseInt(args[0]));
	}
}

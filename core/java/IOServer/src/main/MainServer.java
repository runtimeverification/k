package main;

import log.Logger;
import resources.ResourceSystem;

public class MainServer implements Runnable {
	public int _port;
	public boolean _started;

	public MainServer(int port) {
		_port = port;
		try {
			createDefaultResources();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	public void run() {
		//try {
			//Main.main(new String[] {Integer.toString(_port)});
			// System.out.println("Running server");
			startServer();
			// System.out.println("Got port");
			// _started = true;
		//} catch (Exception e) {
			// TODO Auto-generated catch block
		//	e.printStackTrace();
		//}
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
	
	void startServer() {
		IOServer server = new IOServer(_port);
		_port = server.port; // in case server changes port
		_started = true;
		server.acceptConnections();
	}
	
	public static void main(String[] args) throws Exception {
		MainServer ms = new MainServer(Integer.parseInt(args[0]));
		ms.start();
		//start(Integer.parseInt(args[0]));
	}
}

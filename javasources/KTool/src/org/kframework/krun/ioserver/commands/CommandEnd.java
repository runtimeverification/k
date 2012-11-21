package org.kframework.krun.ioserver.commands;

import java.net.Socket;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.logging.Logger;

public class CommandEnd extends Command {
    private ThreadPoolExecutor pool;
     
    public CommandEnd(String[] args, Socket socket, Logger logger) { 
		super(args, socket, logger); 
	}
     
 	public void setPool(ThreadPoolExecutor pool) { 
 		this.pool = pool;
 	}

	public void run() {
		succeed(new String[] {"Done."});
		pool.shutdownNow();
	}

}

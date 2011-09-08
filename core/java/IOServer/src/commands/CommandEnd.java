package commands;

import java.net.Socket;
import java.util.concurrent.ThreadPoolExecutor;

public class CommandEnd extends Command {
    private ThreadPoolExecutor pool;
     
    public CommandEnd(String[] args, Socket socket) { 
		super(args, socket); 
	}
     
 	public void setPool(ThreadPoolExecutor pool) { 
 		this.pool = pool;
 	}

	public void run() {
		succeed(new String[] {"Done."});
		pool.shutdownNow();
	}

}

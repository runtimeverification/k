package commands;

import java.util.logging.Logger;
import java.net.Socket;

public class CommandUnknown extends Command {


	public CommandUnknown(String[] args, Socket socket, Logger logger) { //, Long maudeId) {
		super(args, socket, logger); //, maudeId);
		// TODO Auto-generated constructor stub
	}

	public void run() {
		fail("unknown command");
	}

}

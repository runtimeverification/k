package commands;

import java.net.Socket;

public class CommandUnknown extends Command {


	public CommandUnknown(String[] args, Socket socket) { //, Long maudeId) {
		super(args, socket); //, maudeId);
		// TODO Auto-generated constructor stub
	}

	public void run() {
		fail("unknown command");
	}

}

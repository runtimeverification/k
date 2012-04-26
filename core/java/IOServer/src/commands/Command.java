package commands;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.logging.Logger;
import main.IOServer;

public abstract class Command implements Runnable {
	Socket socket;
	public int maudeId;
	private Logger _logger;

	public Command(String[] args, Socket socket, Logger logger) { //, Long maudeId) {
		this.socket = socket;
		_logger = logger;
	}

	public void fail(String reason) {
	    _logger.info(maudeId + " is failing because of " + reason);
		IOServer.fail(Integer.toString(maudeId), reason, socket);
	}

	public void succeed(String... messages) {

		String success = maudeId + "#" + "success#";
		for (String s : messages) {
			success += s + "#";
		}
        _logger.info("sending '" + success + "##' to "+ maudeId);
		success += "##\n";
		
		BufferedWriter output;
		try {
			output = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));

			// send data back to client and finish
			output.write(success);
			output.flush();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		try {
			socket.close();
		} catch (Exception e) {
			_logger.info("failed to close socket");
		}
	}
}

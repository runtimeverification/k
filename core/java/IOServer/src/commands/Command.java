package commands;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.Socket;
import log.Logger;

import main.IOServer;

public abstract class Command implements Runnable {

	Socket socket;
	public int maudeId;

	public Command(String[] args, Socket socket) { //, Long maudeId) {
		this.socket = socket;
//		this.maudeId = maudeId;
	}

	public void fail(String reason) {
	    Logger.info(maudeId + " is failing because of " + reason);
		IOServer.fail(Integer.toString(maudeId), reason, socket);
	}

	public void succeed(String... messages) {

		String success = maudeId + "#" + 
			"success#";
		for (String s : messages)
			success += s + "#";
        Logger.info("sending '" + success + "##' to "+ maudeId);
		success += "##\n";
		
		BufferedWriter output;
		try {
			output = new BufferedWriter(new OutputStreamWriter(
					socket.getOutputStream()));

			// send data back to client and finish
			output.write(success);
			output.flush();

			// close everything
			//output.close();
			//socket.close();
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}

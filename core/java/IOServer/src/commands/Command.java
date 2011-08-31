package commands;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.Socket;

import main.IOServer;

public abstract class Command implements Runnable {

	Socket socket;
	//Long maudeId;

	public Command(String[] args, Socket socket) { //, Long maudeId) {
		this.socket = socket;
//		this.maudeId = maudeId;
	}

	public void fail(String reason) {
		IOServer.fail(reason, socket);
	}

	public void succeed(String... messages) {

		String success = //maudeId + "#" + 
			"success#";
		for (String s : messages)
			success += s + "#";
		success += "##\n";
		
		BufferedWriter output;
		try {
			output = new BufferedWriter(new OutputStreamWriter(
					socket.getOutputStream()));

			// send data back to client and finish
			output.write(success);
			output.flush();

			// close everything
			output.close();
			socket.close();
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}

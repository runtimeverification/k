package main;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

import log.Logger;

import commands.Command;
import commands.CommandClose;
import commands.CommandEof;
import commands.CommandFlush;
import commands.CommandOpen;
import commands.CommandPeek;
import commands.CommandPosition;
import commands.CommandReadbyte;
import commands.CommandReopen;
import commands.CommandSeek;
import commands.CommandUnknown;
import commands.CommandWritebyte;
import commands.CommandEnd;

public class IOServer {

	int port;
	ServerSocket serverSocket;
	ThreadPoolExecutor pool;
	// private String END_OF_MESSAGE = "eom";
	private int POOL_THREADS_SIZE = 10;

	public IOServer(int port) {
		
		this.port = port;
		serverSocket = null;
		pool = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(POOL_THREADS_SIZE);

		// new server
		createServer();
	}

	public void createServer() {
		try {
			serverSocket = new ServerSocket(port);
		} catch (IOException e) {
			Logger.severe("Could not listen on port: " + port);
			Logger.severe("This program will exit with error code: 1");
			System.exit(1);
		}
	}

	public void acceptConnections() {
		Logger.info("Server started at "
				+ serverSocket.getInetAddress() + ": " + port);
		
		while (true) {
			Socket clientSocket = null;
			try {

				// accept
				clientSocket = serverSocket.accept();
				Logger.info(clientSocket.toString());

				// parse input
				Command command = parseCommand(clientSocket);

				// execute command == append it to pool
				if (command != null)
					pool.execute(command);

			} catch (IOException e) {
				Logger.severe("Error accepting connection for client on port "
								+ port);
			}
		}
	}

	/**
	 * Read input from a socket until end of message found. Then, parse the
	 * command and return a Command object.
	 * 
	 * @param clientSocket
	 * @return
	 */
	private Command parseCommand(Socket clientSocket) {
		try {
			BufferedReader reader = new BufferedReader(new InputStreamReader(
					clientSocket.getInputStream()));

			String inputLine = reader.readLine();
			
			Logger.info("received request: " + inputLine);
			
			// parse
			// TODO: here XML should be used...
			// maudeId#command#args#
			String[] args = inputLine.split("#");
			String[] args1 = new String[args.length];
			
			System.arraycopy(args, 1, args1,0, args.length-1);
			
			Command command = createCommand(args1, clientSocket);
            
            command.maudeId = Integer.parseInt(args[0]);
			return command;

		} catch (IOException e) {
			return new CommandUnknown(new String[] { e.getLocalizedMessage() },
					clientSocket);
		}
	}

	/***
	 * Parse the input command which looks like: command#arg1#arg2#...
	 * @param args
	 * @param socket
	 * @return the corresponding Command(thread or task) for the given command
	 */
	private Command createCommand(String[] args, Socket socket) {

		// fail if wrong arguments are given
		String command = null;
		if (args.length >= 1)
			command = args[0];
		else 
			fail("Empty command", socket);
		
		
		// switch on command and create appropriate objects
		if (command.equals("open")) {
			return new CommandOpen(args, socket); //, maudeId);
		}
		if (command.equals("reopen")) {
			return new CommandReopen(args, socket); //, maudeId);
		}
		if (command.equals("close")) {
			return new CommandClose(args, socket); //, maudeId);
		}
		if (command.equals("seek")) {
			return new CommandSeek(args, socket); //, maudeId);
		}
		if (command.equals("position")) {
			return new CommandPosition(args, socket); //, maudeId);
		}
		if (command.equals("readbyte")) {
			return new CommandReadbyte(args, socket); //, maudeId);
		}
		if (command.equals("writebyte")) {
			return new CommandWritebyte(args, socket); //, maudeId);
		}
		if (command.equals("flush")) {
			return new CommandFlush(args, socket); //, maudeId);
		}
		if (command.equals("peek")) {
			return new CommandPeek(args, socket); //, maudeId);
		}
		if (command.equals("eof")) {
			return new CommandEof(args, socket); //, maudeId);
		}
		if (command.equals("end")) {
		    CommandEnd c = new CommandEnd(args, socket);
		    c.setPool(pool);
		    return c;
		}

		return new CommandUnknown(args, socket); //, (long) 0);
	}

	/***
	 * Send a failure message to socket specifying also the reason.
	 * @param reason
	 * @param socket
	 */
	public static void fail(String msgId, String reason, Socket socket) {
		
		reason = msgId + "#fail#" + reason + "###\n";
		
		BufferedWriter output;
		try {
			output = new BufferedWriter(new OutputStreamWriter(
					socket.getOutputStream()));

			// send data back to client and finish
			output.write(reason);
			output.flush();

			// close everything
			output.close();
			socket.close();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static void fail(String reason, Socket socket) {
		fail("-1", reason, socket);
	}
}

/*
 * 1. server fisiere - accepta command -> execute
 * 
 * accept(Command c) { c.execute(lookup(c.ID));
 * 
 * /*
 * 
 * mesaj === comanda
 * 
 * 1. open(uri, attr) success: ID fail: string: ""
 * 
 * 2. resopen(ID, uri, attr) success fail: string
 * 
 * 3. close(ID) success fail
 * 
 * 4. seek(ID, pos) success fail
 * 
 * 4'. position(ID) success fail ?
 * 
 * 
 * 5. readbyte(ID) return ASCII fail: EOF
 * 
 * 6. writechar(ID) success fail
 * 
 * 7. flush(ID) success fail
 * 
 * 8. peek(ID) success: ASCII fail
 */
// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.main;

import org.kframework.kil.loader.Context;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.commands.*;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.net.InetSocketAddress;
import java.net.Socket;
import java.nio.channels.ClosedByInterruptException;
import java.nio.channels.ServerSocketChannel;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.logging.Logger;


public class IOServer {
    int port;
    ServerSocketChannel serverSocket;
    ThreadPoolExecutor pool;
    private int POOL_THREADS_SIZE = 10;
    private Logger _logger;
    protected Context context;
    protected FileSystem fs;

    public IOServer(int port, Logger logger, Context context, FileSystem fs) {
        this.context = context;
        this.fs = fs;
        this.port = port;
        _logger = logger;
        pool = (ThreadPoolExecutor) Executors.newFixedThreadPool(POOL_THREADS_SIZE);
        createServer();
    }

    public void createServer() {
        try {
            serverSocket = ServerSocketChannel.open();
            serverSocket.socket().bind(new InetSocketAddress(port));
            this.port = serverSocket.socket().getLocalPort();
        } catch (IOException e) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "IO Server could not listen on port " + port));
        }
    }

    public void acceptConnections() throws IOException {
        _logger.info("Server started at " + serverSocket.socket().getInetAddress() + ": " + port);
        try {
            while (true) {
                Socket clientSocket = serverSocket.socket().accept();
                _logger.info(clientSocket.toString());
                String msg = getMessage(clientSocket);
                Command command = parseCommand(msg, clientSocket);

                // execute command == append it to pool
                if (command != null) {
                    pool.execute(command);
                }
            }
        } catch (ClosedByInterruptException e) {
            //runner has exited, so this thread needs to terminate
            pool.shutdown();
        }
    }

    private String getMessage(Socket clientSocket) throws IOException {
        StringWriter writer = new StringWriter();
        BufferedReader reader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
        int n = 0;
        while (n < 2) {
            int c = reader.read();
            writer.write(c);
            if (c == (int)'\001') {
                n++;
            }
        }
        String inputLine = writer.toString();
        int length = Integer.parseInt(inputLine.split("\001")[1]);
        char[] buffer = new char[length];
        int numRead = reader.read(buffer, 0, length);
        writer.write(buffer, 0, numRead);
        inputLine = writer.toString();

        if (inputLine == null) {
            throw new IOException("Tried to read a line, but was already at EOF");
        }
        return inputLine;
    }

    /**
     * Read input from a socket until end of message found. Then, parse the
     * command and return a Command object.
     *
     * @param clientSocket
     * @return
     */
    private Command parseCommand(String msg, Socket clientSocket) {
        String inputLine = msg;

        _logger.info("received request: " + inputLine);

        // parse
        // TODO: here XML should be used...
        // maudeId#command#args#
        String[] args = inputLine.split("\001", -1);
        String[] args1 = new String[args.length];

        System.arraycopy(args, 2, args1, 0, args.length-2);

        Command command = createCommand(args1, clientSocket, _logger);

        command.maudeId = Integer.parseInt(args[0]);
        return command;
    }


    /***
     * Parse the input command which looks like: command#arg1#arg2#...
     * @param args
     * @param socket
     * @return the corresponding Command(thread or task) for the given command
     */
    public Command createCommand(String[] args, Socket socket, Logger logger) {

        // fail if wrong arguments are given
        String command = null;
        if (args.length >= 1) {
            command = args[0];
        } else {
            fail("Empty command", socket);
        }

        // switch on command and create appropriate objects
        if (command.equals("open")) {
            return new CommandOpen(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("close")) {
            return new CommandClose(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("seek")) {
            return new CommandSeek(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("position")) {
            return new CommandPosition(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("readbyte")) {
            return new CommandReadbyte(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("readbytes")) {
            return new CommandReadbytes(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("writebyte")) {
            return new CommandWritebyte(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("writebytes")) {
            return new CommandWritebytes(args, socket, logger, fs); //, maudeId);
        }
        if (command.equals("stat")) {
            return new CommandStat(args, socket, logger, fs);
        }
        if (command.equals("opendir")) {
            return new CommandOpendir(args, socket, logger, fs);
        }
        if (command.equals("end")) {
            CommandEnd c = new CommandEnd(args, socket, logger, fs);
            c.setPool(pool);
            return c;
        }
        if (command.equals("parse")) {
            return new CommandParse(args, socket, logger, context, fs);
        }

        return new CommandUnknown(args, socket, logger, fs); //, (long) 0);
    }

    /***
     * Send a failure message to socket specifying also the reason.
     * @param reason
     * @param socket
     */
    public static void fail(String msgId, String reason, Socket socket) {

        reason = msgId + "\001fail\001" + reason + "\001\001\001\n";
        //System.out.println(reason);
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
        } catch (IOException e) {
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

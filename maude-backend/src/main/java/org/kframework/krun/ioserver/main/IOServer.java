// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.main;

import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.commands.*;
import org.kframework.utils.errorsystem.KExceptionManager;
import com.google.inject.Inject;

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


public class IOServer implements Runnable {
    private ServerSocketChannel serverSocket;
    private ThreadPoolExecutor pool;
    private static final int POOL_THREADS_SIZE = 10;
    private final Context context;
    private final FileSystem fs;
    private final ConfigurationCreationOptions options;
    private final RunProcess rp;
    private final KExceptionManager kem;
    private int port;

    @Inject
    public IOServer(Context context, FileSystem fs, ConfigurationCreationOptions options, RunProcess rp, KExceptionManager kem) {
        this.context = context;
        this.fs = fs;
        this.options = options;
        this.rp = rp;
        this.kem = kem;
    }

    public int getPort() {
        return port;
    }

    public void createServer() {
        pool = (ThreadPoolExecutor) Executors.newFixedThreadPool(POOL_THREADS_SIZE);
        try {
            serverSocket = ServerSocketChannel.open();
            serverSocket.socket().bind(new InetSocketAddress(port));
            this.port = serverSocket.socket().getLocalPort();
        } catch (IOException e) {
            throw KExceptionManager.criticalError("IO Server could not listen on port " + port, e);
        }
    }

    public void acceptConnections() throws IOException {
        try {
            while (true) {
                Socket clientSocket = serverSocket.socket().accept();
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

        // parse
        // TODO: here XML should be used...
        // maudeId#command#args#
        String[] args = inputLine.split("\001", -1);
        String[] args1 = new String[args.length];

        System.arraycopy(args, 2, args1, 0, args.length-2);

        Command command = createCommand(args1, clientSocket);

        command.maudeId = Integer.parseInt(args[0]);
        return command;
    }


    /***
     * Parse the input command which looks like: command#arg1#arg2#...
     * @param args
     * @param socket
     * @return the corresponding Command(thread or task) for the given command
     */
    public Command createCommand(String[] args, Socket socket) {

        // fail if wrong arguments are given
        String command = null;
        if (args.length >= 1) {
            command = args[0];
        } else {
            fail("Empty command", socket);
        }

        // switch on command and create appropriate objects
        if (command.equals("open")) {
            return new CommandOpen(args, socket, fs); //, maudeId);
        }
        if (command.equals("close")) {
            return new CommandClose(args, socket, fs); //, maudeId);
        }
        if (command.equals("seek")) {
            return new CommandSeek(args, socket, fs); //, maudeId);
        }
        if (command.equals("position")) {
            return new CommandPosition(args, socket, fs); //, maudeId);
        }
        if (command.equals("readbyte")) {
            return new CommandReadbyte(args, socket, fs); //, maudeId);
        }
        if (command.equals("readbytes")) {
            return new CommandReadbytes(args, socket, fs); //, maudeId);
        }
        if (command.equals("writebyte")) {
            return new CommandWritebyte(args, socket, fs); //, maudeId);
        }
        if (command.equals("writebytes")) {
            return new CommandWritebytes(args, socket, fs); //, maudeId);
        }
        if (command.equals("stat")) {
            return new CommandStat(args, socket, fs);
        }
        if (command.equals("opendir")) {
            return new CommandOpendir(args, socket, fs);
        }
        if (command.equals("end")) {
            CommandEnd c = new CommandEnd(args, socket, fs);
            c.setPool(pool);
            return c;
        }
        if (command.equals("parse")) {
            return new CommandParse(args, socket, context, fs, options, rp, kem);
        }
        if (command.equals("system")) {
            return new CommandSystem(args, socket, fs, rp);
        }

        return new CommandUnknown(args, socket, fs); //, (long) 0);
    }

    /***
     * Send a failure message to socket specifying also the reason.
     * @param reason
     * @param socket
     */
    public static void fail(String msgId, String reason, Socket socket) {
        System.err.println(reason);
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
            throw KExceptionManager.criticalError("Error writing output to client", e);
        }
    }

    public static void fail(String reason, Socket socket) {
        fail("-1", reason, socket);
    }

    @Override
    public void run() {
        createServer();
        synchronized(this) {
            this.notify();
        }
        try {
            acceptConnections();
        } catch (IOException e) {
            throw KExceptionManager.internalError("Failed to start IO server: " + e.getMessage(), e);
        }

    }
}

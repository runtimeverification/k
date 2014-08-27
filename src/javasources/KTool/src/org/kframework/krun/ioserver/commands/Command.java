// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.main.IOServer;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.logging.Logger;


public abstract class Command implements Runnable {
    Socket socket;
    public int maudeId;
    protected FileSystem fs;
    private Logger _logger;

    public Command(String[] args, Socket socket, Logger logger, FileSystem fs) { //, Long maudeId) {
        this.socket = socket;
        this.fs = fs;
        _logger = logger;
    }

    public void fail(String reason) {
        _logger.info(maudeId + " is failing because of " + reason);
        IOServer.fail(Integer.toString(maudeId), reason, socket);
    }

    public void succeed(String... messages) {
        if (messages.length == 0) {
            messages = new String[] {"success"};
        }
        String success = maudeId + "\001" + "success\001";
        for (String s : messages) {
            success += s + "\001";
        }
        _logger.info("sending '" + success + "\001\001' to "+ maudeId);
        success += "\001\001\n";

        BufferedWriter output = null;
        try {
            output = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));

            // send data back to client and finish
            output.write(success);
            output.flush();
            output.close();
        } catch (IOException e) {
            _logger.info("failed to respond to client " + maudeId);
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        try {
            _logger.info("Closing client socket for " + maudeId);
//            socket.shutdownOutput();
//            if (output != null) {output.close();}
            Thread.sleep(100);   // There should exist a better solution for this problem
            socket.close();
        } catch (IOException e) {
            _logger.info("failed to close socket for " + maudeId);
            e.printStackTrace();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }
}

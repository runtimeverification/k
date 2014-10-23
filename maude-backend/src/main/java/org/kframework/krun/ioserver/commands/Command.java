// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.main.IOServer;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.Socket;


public abstract class Command implements Runnable {
    Socket socket;
    public int maudeId;
    protected FileSystem fs;

    public Command(String[] args, Socket socket, FileSystem fs) { //, Long maudeId) {
        this.socket = socket;
        this.fs = fs;
    }

    public void fail(String reason) {
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
        success += "\001\001\n";

        BufferedWriter output = null;
        try {
            output = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));

            // send data back to client and finish
            output.write(success);
            output.flush();
            output.close();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        try {
            Thread.sleep(100);   // There should exist a better solution for this problem
            socket.close();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }
}

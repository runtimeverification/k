// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;

public class CommandReadbyte extends Command {


    private long ID;

    public CommandReadbyte(String[] args, Socket socket, FileSystem fs) { //, Long maudeId) {
        super(args, socket, fs); //, maudeId);

        try {
            ID = Long.parseLong(args[1]);
        } catch (NumberFormatException nfe) {
            fail("read byte operation aborted: " + nfe.getLocalizedMessage());
        }
    }

    public void run() {
        try {
            succeed(Integer.toString((fs.get(ID).getc() & 0xff)));
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }
}

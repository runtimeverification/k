// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandSeek extends Command {


    private long ID;
    private int position;

    public CommandSeek(String[] args, Socket socket, Logger logger, FileSystem fs) { //, Long maudeId) {
        super(args, socket, logger, fs); //, maudeId);
        
        try {
            ID = Long.parseLong(args[1]);
            position = Integer.parseInt(args[2]);
        } catch (NumberFormatException nfe) {
            fail("seek operation aborted: " + nfe.getLocalizedMessage());
        }
    }

    public void run() {
        try {
            fs.get(ID).seek(position);
            succeed();
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }

}

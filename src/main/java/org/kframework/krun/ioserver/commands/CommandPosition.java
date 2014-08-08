// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandPosition extends Command {


    private long ID;

    public CommandPosition(String[] args, Socket socket, Logger logger, FileSystem fs) { //, Long maudeId) {
        super(args, socket, logger, fs); //, maudeId);

        try {
            ID = Long.parseLong(args[1]);
        } catch (NumberFormatException nfe) {
            fail("position operation aborted: " + nfe.getLocalizedMessage());
        }
    }

    public void run() {
        try {
            succeed(Long.toString(fs.get(ID).tell()));
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }
}

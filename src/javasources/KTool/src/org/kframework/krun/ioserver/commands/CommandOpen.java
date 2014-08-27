// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;


public class CommandOpen extends Command {

    private String path;
    private String mode;

    public CommandOpen(String[] args, Socket socket, Logger logger, FileSystem fs) { //, Long maudeId) {
        super(args, socket, logger, fs); //, maudeId);

        // uri#attribute1=v1#a2=v2...
        path = args[1];
        mode = args[2];
    }

    public void run() {
        try {
            succeed(Long.toString(fs.open(path, mode)));
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }

}

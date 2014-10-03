// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandReadbytes extends Command {

    private long ID;
    private int numBytes;

    public CommandReadbytes(String[] args, Socket socket, Logger logger, FileSystem fs) {
        super(args, socket, logger, fs);

        try {
            ID = Long.parseLong(args[1]);
            numBytes = Integer.parseInt(args[2]);
        } catch (NumberFormatException nfe) {
            fail("read bytes operation aborted: " + nfe.getLocalizedMessage());
        }
    }

    public void run() {
        try {
           succeed(new String(fs.get(ID).read(numBytes)));
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }
}

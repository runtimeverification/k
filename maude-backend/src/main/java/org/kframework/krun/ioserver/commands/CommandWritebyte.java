// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandWritebyte extends Command {


    private long ID;
    private byte ascii;

    public CommandWritebyte(String[] args, Socket socket, Logger logger, FileSystem fs) { //, Long maudeId) {
        super(args, socket, logger, fs); //, maudeId);

        try {
            ID = Long.parseLong(args[1]);
            // ascii = Byte.parseByte(args[2]);
            int signedByte = Integer.parseInt(args[2]);
            ascii = (byte)signedByte;
        } catch (NumberFormatException nfe) {
            fail("write operation aborted: " + nfe.getLocalizedMessage());
        }
    }

    public void run() {
        try {
            fs.get(ID).putc(ascii);
            succeed();
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }

}

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;
import java.util.logging.Logger;

public class CommandWritebytes extends Command {


    private long ID;
    private String string;
    private byte[] bytes;

    public CommandWritebytes(String[] args, Socket socket, Logger logger, FileSystem fs) { //, Long maudeId) {
        super(args, socket, logger, fs); //, maudeId);

        try {
            ID = Long.parseLong(args[1]);
            // ascii = Byte.parseByte(args[2]);
            string = "";
            String conn = "";
            for (int i = 2; i < args.length - 3; i++) {
                string += conn + args[i];
                conn = "\001";
            }
            bytes = string.getBytes();
        } catch (NumberFormatException nfe) {
            fail("write operation aborted: " + nfe.getLocalizedMessage());
        }
    }

    public void run() {
        try {
            fs.get(ID).write(bytes);
            succeed();
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }

}

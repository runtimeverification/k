// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.net.Socket;



public class CommandClose extends Command {

    private Long ID;

    public CommandClose(String[] args, Socket socket, FileSystem fs) { //, Long maudeId) {

        // the form of the request should be: close#ID
        super(args, socket, fs); //, maudeId);

        try {
            ID = Long.parseLong(args[1]);
        } catch (NumberFormatException nfe) {
            fail("close operation aborted: " + nfe.getLocalizedMessage());
        }
    }

    public void run() {
        try {
            fs.close(ID);
            succeed();
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }

}

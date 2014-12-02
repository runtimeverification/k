// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.time.Instant;

public class CommandTime extends Command {


    private long milliseconds;

    public CommandTime(String[] args, Socket socket, FileSystem fs) { //, Long maudeId) {
        super(args, socket, fs); //, maudeId);

        try {
            milliseconds = Instant.Now.toEpochMilli();
        } catch (ArithmeticException ae) {
            fail("numeric overflow of time: " + ae.getLocalizedMessage());
        }
    }

    public void run() {
		succeed(Long.toString(milliseconds);
    }
}

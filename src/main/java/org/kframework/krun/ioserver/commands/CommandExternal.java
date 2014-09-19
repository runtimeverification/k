// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;

import java.net.Socket;
import java.util.logging.Logger;
import java.util.Map;
import java.util.HashMap;

public class CommandExternal extends Command {

    private String[] cmd;
    protected Context context;

    public CommandExternal(String[] args, Socket socket, Logger logger, Context context, FileSystem fs) {
        super(args, socket, logger, fs);
        this.context = context;

        int length = args.length - 1 - 3 /* garbage */;
        cmd = new String[length];
        System.arraycopy(args, 1, cmd, 0, length);
    }

    public void run() {
      //for (String c : cmd) { System.out.println(c); }
        RunProcess rp = new RunProcess();
        Map<String, String> environment = new HashMap<>();
        rp.execute(environment, cmd);

        if (rp.getExitCode() == 0) {
            String result = rp.getStdout() != null ? rp.getStdout() : "";
            succeed(result.trim());
        } else {
            fail("failed: returned a non-zero exit code: " + rp.getExitCode() +
                " Stdout: " + rp.getStdout() + " Stderr: " + rp.getErr());
        }
    }
}

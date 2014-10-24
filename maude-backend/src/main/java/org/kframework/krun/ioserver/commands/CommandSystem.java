// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.RunProcess;
import org.kframework.krun.RunProcess.ProcessOutput;
import org.kframework.krun.api.io.FileSystem;
import java.net.Socket;
import java.util.Map;
import java.util.HashMap;

public class CommandSystem extends Command {

    private String[] cmd;
    private final RunProcess rp;

    public CommandSystem(String[] args, Socket socket, FileSystem fs, RunProcess rp) {
        super(args, socket, fs);
        this.rp = rp;

        int length = args.length - 1 - 3 /* garbage */;
        cmd = new String[length];
        System.arraycopy(args, 1, cmd, 0, length);
    }

    public void run() {
        Map<String, String> environment = new HashMap<>();
        ProcessOutput output = rp.execute(environment, cmd);

        String stdout = output.stdout != null ? output.stdout : "";
        String stderr = output.stderr != null ? output.stderr : "";
        succeed(Integer.toString(output.exitCode), stdout.trim(), stderr.trim(), "#EOL");
    }
}

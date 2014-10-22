// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.krun.api.io.FileSystem;

import java.net.Socket;
import java.util.concurrent.ThreadPoolExecutor;

public class CommandEnd extends Command {
    private ThreadPoolExecutor pool;

    public CommandEnd(String[] args, Socket socket, FileSystem fs) {
        super(args, socket, fs);
    }

     public void setPool(ThreadPoolExecutor pool) {
         this.pool = pool;
     }

    public void run() {
        succeed(new String[] {"Done."});
        pool.shutdownNow();
    }

}

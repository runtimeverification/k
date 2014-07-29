// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;

import java.net.Socket;
import java.util.logging.Logger;

public class CommandParse extends Command {

    private String stringToParse;
    private String sort;
    protected Context context;

    public CommandParse(String[] args, Socket socket, Logger logger, Context context, FileSystem fs) {
        super(args, socket, logger, fs);
        this.context = context;

        sort = args[1];
        stringToParse = args[2];
    }

    public void run() {
        try {
            RunProcess rp = new RunProcess();
            Term kast = rp.runParser(context.krunOptions.configurationCreation.parser(context), stringToParse, true, sort, context);
            MaudeFilter mf = new MaudeFilter(context);
            mf.visitNode(kast);
            succeed(mf.getResult().toString());
        } catch (ParseFailedException e) {
            fail("noparse");
        }
    }
}

// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;

import java.net.Socket;

public class CommandParse extends Command {

    private String stringToParse;
    private Sort sort;
    private final Context context;
    private final ConfigurationCreationOptions options;

    public CommandParse(String[] args, Socket socket, Context context, FileSystem fs, ConfigurationCreationOptions options) {
        super(args, socket, fs);
        this.context = context;
        this.options = options;

        sort = Sort.of(args[1]);
        stringToParse = args[2];
    }

    public void run() {
        try {
            RunProcess rp = new RunProcess();
            Term kast = rp.runParser(options.parser(context), stringToParse, true, sort, context);
            MaudeFilter mf = new MaudeFilter(context);
            mf.visitNode(kast);
            succeed(mf.getResult().toString());
        } catch (ParseFailedException e) {
            fail("noparse");
        }
    }
}

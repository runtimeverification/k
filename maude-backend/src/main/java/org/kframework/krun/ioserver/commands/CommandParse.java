// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.commands;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.net.Socket;

public class CommandParse extends Command {

    private String stringToParse;
    private Sort sort;
    private final Context context;
    private final ConfigurationCreationOptions options;
    private final RunProcess rp;
    private final KExceptionManager kem;

    public CommandParse(String[] args, Socket socket,
            Context context,
            FileSystem fs,
            ConfigurationCreationOptions options,
            RunProcess rp,
            KExceptionManager kem) {
        super(args, socket, fs);
        this.context = context;
        this.options = options;
        this.rp = rp;
        this.kem = kem;

        sort = Sort.of(args[1]);
        stringToParse = args[2];
    }

    public void run() {
        try {
            Term kast = rp.runParser(options.parser(context), stringToParse, true, sort, context);
            MaudeFilter mf = new MaudeFilter(context, kem);
            mf.visitNode(kast);
            succeed(mf.getResult().toString());
        } catch (ParseFailedException e) {
            fail("noparse");
        }
    }
}

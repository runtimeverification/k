package org.kframework.krun.ioserver.commands;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.kil.Term;
import org.kframework.krun.K;
import org.kframework.krun.RunProcess;

import java.net.Socket;
import java.util.logging.Logger;

public class CommandParse extends Command {

	private String stringToParse;
	private String sort;

	public CommandParse(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);

		sort = args[1];
		stringToParse = args[2];
	}

	public void run() {
		RunProcess rp = new RunProcess();
		Term kast = rp.runParser(K.parser, stringToParse, true, sort);
		MaudeFilter mf = new MaudeFilter();
		kast.accept(mf);
		succeed(new String[] { mf.getResult() });
	}
}

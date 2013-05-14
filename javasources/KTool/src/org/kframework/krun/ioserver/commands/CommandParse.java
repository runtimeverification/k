package org.kframework.krun.ioserver.commands;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.K;
import org.kframework.krun.RunProcess;

import java.net.Socket;
import java.util.logging.Logger;

public class CommandParse extends Command {

	private String stringToParse;
	private String sort;
	protected DefinitionHelper definitionHelper;

	public CommandParse(String[] args, Socket socket, Logger logger, DefinitionHelper definitionHelper) {
		super(args, socket, logger);
		this.definitionHelper = definitionHelper;

		sort = args[1];
		stringToParse = args[2];
	}

	public void run() {
		try {
			RunProcess rp = new RunProcess();
			Term kast = rp.runParser(K.parser, stringToParse, true, sort, definitionHelper);
			MaudeFilter mf = new MaudeFilter(definitionHelper);
			kast.accept(mf);
			succeed(new String[] { mf.getResult() });
		} catch (TransformerException e) {
			fail("noparse");
		}
	}
}

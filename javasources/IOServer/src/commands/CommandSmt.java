package commands;

import java.net.Socket;
import java.util.logging.Logger;

import jfkbits.LispParser;
import jfkbits.LispParser.Expr;
import jfkbits.LispTokenizer;
import resources.ResourceSmt;
import resources.ResourceSystem;

public class CommandSmt extends Command {

	private long ID;
	private String smtlib;

	public CommandSmt(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);
		try {
			ID = Long.parseLong(args[1]);
			smtlib = args[2];
		} catch (NumberFormatException nfe) {
			fail("smt connection aborted: " + nfe.getLocalizedMessage());
		}

	}

	public void run()
	{
		// retrieve file struct
		ResourceSmt resource = (ResourceSmt)ResourceSystem.getResource(ID);

		// call corresponding method on file
		try {
			resource.sendToInput(smtlib);
			String output = resource.getFromOutput();

			// parsing
			LispTokenizer lt = new LispTokenizer(output);
			LispParser lp = new LispParser(lt);
			try{
				Expr parsed = lp.parseExpr();
				String out = parsed.getKIF().trim();
				if (out.trim().equals("")){
					//System.out.println("EMPTY: >>" + out + "<<");
				} else output = out;
			}
			catch(Exception e){
				fail("unknown");
			}
			
			// success
			succeed(new String[] { output.toString() });

		} catch (Exception e) {
			// TODO Auto-generated catch block
			fail("Smt problem " + ID);
			e.printStackTrace();
		}
	}
}

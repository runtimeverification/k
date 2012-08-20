package commands;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Logger;

public class CommandSmt extends Command {

	String[] args;

	public CommandSmt(String[] args, Socket socket, Logger logger) {
		super(args, socket, logger);
		this.args = args;
	}

	public void run() {

		try {
			String smt = args[1]; // hope this doesn't crashes...
//			for (int i = 0; i < args.length; i++)
//				System.out.println(args[i]);

			String filename = File.createTempFile("smt", ".smt2").getName();
			String toExecute = createSmtFile(smt, filename);

			// run z3 on filename
			String result = z3(filename);
//			System.out.println("Created:" + toExecute + "\nExecution: " + result + "\n\n");
			// delete filename
			new File(filename).delete();
			
			succeed(new String[] { result });
		} catch (IOException e) {
			System.out.println("Error " + e.getMessage());
		}
	}

	public String createSmtFile(String smtlib, String filename) {
		String smt = "";
		try {
			FileWriter fstream = new FileWriter(filename);
			BufferedWriter out = new BufferedWriter(fstream);

			String[] smtStmts = smtlib.split("(?<=\\))\\s+(?=\\()");
			String smtcmd = "";
			List<String> bag = new LinkedList<String>();
			for (int i = 0; i < smtStmts.length; i++) {
				if (bag.contains(smtStmts[i].trim()))
					continue;
				bag.add(smtStmts[i].trim());
				smtcmd += smtStmts[i] + "\n";
			}

			smt = smtcmd;
			out.write(smtcmd);
			out.close();
		} catch (Exception e) {// Catch exception if any
			System.err.println("Error: " + e.getMessage());
		}
		return smt;
	}
	
	private String z3(String filename) {
		
		String z3exe = "z3"; // assume that z3 can be run directly from command line
		String out = "";
		
		ProcessBuilder pb = new ProcessBuilder(z3exe, filename);
		try {
			Process p = pb.start();
			
			BufferedReader output = new BufferedReader (new InputStreamReader(p.getInputStream()));
			BufferedReader error = new BufferedReader (new InputStreamReader(p.getErrorStream()));
			
			String line = "";
			while((line = output.readLine())!=null)
			{
				out += line + "\n";
			}
			while((line = error.readLine())!=null)
			{
				out += line + "\n";
			}
			
			p.destroy();
		} catch (IOException e) {
			out += "Error while executing z3: " + e.getMessage();
		}
		
		return out;
	}


}

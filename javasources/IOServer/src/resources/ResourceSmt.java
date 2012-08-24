package resources;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class ResourceSmt extends Resource{
	String solver;
	Process smt;
	
	public ResourceSmt(String solver) {
		this.solver = solver;
		
		// initialize the process, set the input and the output
		ProcessBuilder pb = new ProcessBuilder("z3", "-smt2", "-in");
		try {
			smt = pb.start();
			
			// send print success
			sendToInput("(set-option :print-success true)"); 
			getFromOutput();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	@Override
	public void close() throws Exception {
		smt.destroy();
	}

	@Override
	public void sendToInput(String s) throws Exception {
//		System.out.println("Sending: " + s);
		BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(smt.getOutputStream()));
		bw.write(s);
		bw.write(System.getProperty("line.separator"));
		bw.flush();
	}

	@Override
	public String getFromOutput() throws Exception {
		BufferedReader br = new BufferedReader(new InputStreamReader(smt.getInputStream()));
		
		String output = "";
		String line = "";
		output = br.readLine();
		if (!output.startsWith("("))
			return output;
		
		while((line = br.readLine()) != null)
		{
			output += line;
			if (line.startsWith(")"))
				break;
		}
		
		return output;
	}
	
	
}

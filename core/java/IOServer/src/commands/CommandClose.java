package commands;

import java.net.Socket;

import resources.Resource;
import resources.ResourceSystem;


public class CommandClose extends Command {

	private Long ID;

	public CommandClose(String[] args, Socket socket) { //, Long maudeId) {

		// the form of the request should be: close#ID
		super(args, socket); //, maudeId);

		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("close operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {

		// retrieve file struct
		Resource resource = ResourceSystem.getResource(ID);

		// call corresponding method on resource
		try {
			resource.close();

			ResourceSystem.remove(ID);
			
			// success
			succeed(new String[] { "success" });
		} catch (Exception e) {
			// TODO Auto-generated catch block
			fail("Cannot close resource " + ID);
			e.printStackTrace();
		}

	}

}

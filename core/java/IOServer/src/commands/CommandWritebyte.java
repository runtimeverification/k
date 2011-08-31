package commands;

import java.net.Socket;

import resources.Resource;
import resources.ResourceSystem;

public class CommandWritebyte extends Command {


	private long ID;
	private byte ascii;

	public CommandWritebyte(String[] args, Socket socket) { //, Long maudeId) {
		super(args, socket); //, maudeId);

		try {
			ID = Long.parseLong(args[1]);
			ascii = Byte.parseByte(args[2]);
		} catch (NumberFormatException nfe) {
			fail("write operation aborted: " + nfe.getLocalizedMessage());
		}
	}

	public void run() {
		
		// get resource
		Resource resource = ResourceSystem.getResource(ID);
		
		try {
			resource.writebyte(ascii);
			succeed(new String[] { "success" });
		} catch (Exception e) {
			fail("seek: cannot write " + ascii + " in resource " + ID);
		}
	}

}

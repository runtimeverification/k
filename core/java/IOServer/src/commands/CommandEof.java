package commands;

import java.net.Socket;

import resources.Resource;
import resources.ResourceSystem;

public class CommandEof extends Command {

	private long ID;

	public CommandEof(String[] args, Socket socket) {
		super(args, socket);

		try {
			ID = Long.parseLong(args[1]);
		} catch (NumberFormatException nfe) {
			fail("eof operation aborted: " + nfe.getLocalizedMessage());
		}
}

	public void run() {
		try{
			Resource resource = ResourceSystem.getResource(ID);
			Byte bite = resource.eof();
			succeed(new String[] { bite.toString() });
		}
		catch (Exception e)
		{
			fail(e.getLocalizedMessage());
		}
	}

}

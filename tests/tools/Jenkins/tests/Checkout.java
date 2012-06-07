import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;

import org.junit.Test;

public class Checkout {

	@Test
	public void checkout() throws InterruptedException, URISyntaxException {

		StaticK.file = new File(getClass().getProtectionDomain()
				.getCodeSource().getLocation().toURI().getPath());
		StaticK.toolsDir = StaticK.file.getAbsolutePath().replaceFirst(
				"/Jenkins.*?$", "");

		// first, checkout K -> verify the existence of k-framework dir.
		System.out.print("\nRetrieving K ...");
		String[] commands = new String[] { "svn", "export",
				"https://k-framework.googlecode.com/svn/trunk", StaticK.kbase };
		Executor executor = new Executor(commands, ".");
		executor.start();
		executor.join(StaticK.ulimit * 1000);
		Thread.yield();
		assertTrue(new File(StaticK.kbase).exists());
		System.out.println("Done.");
	}
}

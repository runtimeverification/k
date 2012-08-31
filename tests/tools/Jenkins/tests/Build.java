import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;

import org.junit.Test;

public class Build {

	@Test
	public void build() throws InterruptedException, URISyntaxException {
	// build K -> verify if the k3.jar file was created
		String[] commands = new String[] { "ant" };
		System.out.print("\nBuild ...");
		Executor build = new Executor(commands, StaticK.kbasedir, null, StaticK.ulimit);
		build.start();
		build.join(0);
		Thread.yield();
		StaticK.k3Jar = StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "k3.jar";
		StaticK.JKrun = StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "JKrun.jar";
		
		assertTrue(new File(StaticK.k3Jar).exists());
		assertTrue(new File(StaticK.JKrun).exists());

		if (!new File(StaticK.k3Jar).exists())
			System.exit(1);
		if (!new File(StaticK.JKrun).exists())
			System.exit(1);
			
		System.out.println("\n\n" + build.getOutput());
		
		System.out.println("\n\nDone.");
	}
}

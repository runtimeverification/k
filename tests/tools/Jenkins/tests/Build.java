import static org.junit.Assert.*;

import java.io.File;
import java.net.URISyntaxException;

import org.junit.Test;


public class Build {

	@Test
	public void build() throws InterruptedException, URISyntaxException {
	// build K -> verify if the k3.jar file was created
		String[] commands = new String[] { "ant" };
		System.out.print("Build ...");
		Executor build = new Executor(commands, StaticK.toolsDir + StaticK.fileSep + "Jenkins" + StaticK.fileSep + StaticK.kbase);
		build.start();
		build.join(StaticK.ulimit * 1000);
		Thread.yield();
		StaticK.k3Jar = StaticK.toolsDir + StaticK.fileSep + "Jenkins" + StaticK.fileSep + StaticK.kbase + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "k3.jar";
		assertTrue(new File(StaticK.k3Jar).exists());
		System.out.println("Done.");
	}
}

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;

import org.junit.Test;

public class Build {

	@Test
	public void build() throws InterruptedException, URISyntaxException {
	// build K -> verify if the k3.jar file was created
		String[] commands = new String[] { "ant" , "all", "java", "jar" };
		System.out.print("\nBuild ...");
		Executor build = new Executor(commands, StaticK.toolsDir + StaticK.fileSep + "Jenkins" + StaticK.fileSep + StaticK.kbase);
		build.start();
		build.join(StaticK.ulimit * 1000);
		Thread.yield();
		StaticK.k3Jar = StaticK.toolsDir + StaticK.fileSep + "Jenkins" + StaticK.fileSep + StaticK.kbase + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "k3.jar";
		StaticK.JKrun = StaticK.toolsDir + StaticK.fileSep + "Jenkins" + StaticK.fileSep + StaticK.kbase + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "JKrun.jar";
		
		assertTrue(new File(StaticK.k3Jar).exists());
		assertTrue(new File(StaticK.JKrun).exists());
		
		System.out.println("\tDone.");
	}
}

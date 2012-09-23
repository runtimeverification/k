import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;

import java.io.File;
import java.net.URISyntaxException;

import org.junit.Test;

public class Checkout {

	@Test
	public void allTests() throws URISyntaxException
	{
		System.out.println("Using " + StaticK.initPoolSize() + " core(s).");
		
		StaticK.file = new File(getClass().getProtectionDomain()
				.getCodeSource().getLocation().toURI().getPath());
		StaticK.toolsDir = StaticK.file.getAbsolutePath().replaceFirst(
				"/Jenkins.*?$", "");
		StaticK.kbasedir = StaticK.toolsDir + StaticK.fileSep + "Jenkins" + StaticK.fileSep + StaticK.kbase;

		assertTrue(new File(StaticK.toolsDir).exists());
	}

	@Test
	public void checkout() throws InterruptedException, URISyntaxException {

		// first, copy K -> verify the existence of k-framework dir.
		
		System.out.print("\nRemoving old K artifacts ...");
		String[] removeCommands = new String[] { "rm", "-rf", StaticK.kbase };
		Executor rmexecutor = new Executor(removeCommands, ".", null, StaticK.biggerlimit);
		rmexecutor.start();
		rmexecutor.join(StaticK.ulimit * 1000);
		Thread.yield();
		assertFalse(new File(StaticK.kbase).exists());
		System.out.println("Removed.");
		
		System.out.print("Copying K from k-framework project ...");
		String[] copyCommands = new String[] { "cp", "-r", "/var/lib/jenkins/workspace/k-framework" , StaticK.kbase };
		Executor cpexecutor = new Executor(copyCommands, ".", null, StaticK.biggerlimit);
		cpexecutor.start();
		cpexecutor.join(StaticK.ulimit * 1000);
		Thread.yield();
		assertTrue(new File(StaticK.kbase).exists());
		assertTrue(new File(StaticK.kbasedir).exists());
		System.out.println("Copied.");
		
		// delete maude binaries
		System.out.print("Removing maude binaries ...");
		deleteFolder(new File(StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin" + StaticK.fileSep + "maude" + StaticK.fileSep + "binaries"));
		assertFalse(new File(StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin" + StaticK.fileSep + "maude" + StaticK.fileSep + "binaries").exists());
		System.out.println("Removed.");
		
		System.out.println("Done with setup.");
	}
	
	private void deleteFolder(File folder) {
	    File[] files = folder.listFiles();
	    if(files!=null) { //some JVMs return null for empty dirs
	        for(File f: files) {
	            if(f.isDirectory()) {
	                deleteFolder(f);
	            } else {
	                f.delete();
	            }
	        }
	    }
	    folder.delete();
	}
}

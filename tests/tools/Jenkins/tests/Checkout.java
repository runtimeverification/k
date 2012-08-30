import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;

import org.junit.Test;

public class Checkout {

	@Test
	public void allTests() throws URISyntaxException
	{
		System.out.println("Using " + StaticK.THREAD_POOL_SIZE + " processors.");
		
		StaticK.file = new File(getClass().getProtectionDomain()
				.getCodeSource().getLocation().toURI().getPath());
		StaticK.toolsDir = StaticK.file.getAbsolutePath().replaceFirst(
				"/Jenkins.*?$", "");
		StaticK.kbasedir = StaticK.toolsDir + StaticK.fileSep + "Jenkins" + StaticK.fileSep + StaticK.kbase;

		assertTrue(new File(StaticK.toolsDir).exists());
	}

	@Test
	public void checkout() throws InterruptedException, URISyntaxException {

		// first, checkout K -> verify the existence of k-framework dir.
		System.out.print("\nCheckout K ...");
		String[] commands = new String[] { "svn", "checkout",
				"https://k-framework.googlecode.com/svn/trunk", ";" , "ant" , "clean", StaticK.kbase };
		Executor executor = new Executor(commands, ".", null);
		executor.start();
		executor.join(StaticK.ulimit * 1000);
		Thread.yield();
		assertTrue(new File(StaticK.kbase).exists());
		assertTrue(new File(StaticK.kbasedir).exists());
		
		// delete maude binaries
		deleteFolder(new File(StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin" + StaticK.fileSep + "maude" + StaticK.fileSep + "binaries"));
		
		System.out.println("\tDone.");
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

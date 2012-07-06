import org.junit.Test;


public class InitLocal {

	@Test
	public void test() {
		System.out.println("Using " + StaticK.THREAD_POOL_SIZE + " processors.");
		
		String userDir = System.getProperty("user.dir");
		
		StaticK.kbasedir = userDir;
//System.out.println("BASE: " + StaticK.kbasedir);
		StaticK.k3Jar = StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "k3.jar";
		StaticK.JKrun = StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "JKrun.jar";
	}

}

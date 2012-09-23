import org.junit.Test;


public class InitLocal {

	@Test
	public void test() {
		System.out.println("Using " + StaticK.initPoolSize() + " core(s).");
		
		String userDir = System.getProperty("user.dir");
		
		StaticK.kbasedir = userDir;

		StaticK.k3Jar = StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "k3.jar";
	}

}

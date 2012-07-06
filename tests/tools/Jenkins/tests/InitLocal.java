import org.junit.Test;


public class InitLocal {

	@Test
	public void test() {
		String userDir = System.getProperty("user.dir");
		
		StaticK.kbasedir = userDir;

		StaticK.k3Jar = StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "k3.jar";
		StaticK.JKrun = StaticK.kbasedir + StaticK.fileSep + "dist" + StaticK.fileSep + "bin"
				+ StaticK.fileSep + "java" + StaticK.fileSep + "JKrun.jar";
	}

}

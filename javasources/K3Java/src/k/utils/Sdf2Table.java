package k.utils;

import java.io.*;

import ro.uaic.fmse.k2m.main.Kil2Maude;

public class Sdf2Table {

	public static void run_sdf2table(File startDir, String mainFile) {
		ThreadedStreamHandler errorStreamHandler;

		try {
			File f = null;
			String basePath;

			if (Kil2Maude.isDebugMode())
				basePath = Kil2Maude.getKBase(false);
			else
				basePath = "./";
				
			if (isUnixOS()) {
				f = new File(basePath + "/bin/native/linux/sdf2table");
				f.setExecutable(true, false);
			}
			if (isWindowsOS()) {
				f = new File(basePath + "/bin/native/cygwin/sdf2table.exe");
			}
			if (isMacOS()) {
				f = new File(basePath + "/bin/native/macosx/sdf2table");
				f.setExecutable(true, false);
			}

			// create process
			ProcessBuilder pb = new ProcessBuilder(f.getAbsolutePath(), "-c", "-m", mainFile, "-o", mainFile + ".tbl");
			pb.directory(startDir);

			// start sdf2table process
			Process process = pb.start();

			InputStream errorStream = process.getErrorStream();
			// these need to run as java thread to get the standard error from the command.
			errorStreamHandler = new ThreadedStreamHandler(errorStream);
			errorStreamHandler.start();
			process.waitFor();

			String s = errorStreamHandler.getContent().toString();
			// if some errors occurred (if something was written on the stderr stream)
			if (!s.equals("")) {
				System.out.println("Some errors occurred..");
				System.out.println(s);
				// abort the compilation
				System.exit(1);
			}
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}

	private static boolean isUnixOS() {
		String os = System.getProperty("os.name").toLowerCase();
		return os.contains("nix") || os.contains("nux");
	}

	private static boolean isWindowsOS() {
		return System.getProperty("os.name").toLowerCase().contains("win");
	}

	private static boolean isMacOS() {
		return System.getProperty("os.name").toLowerCase().contains("mac");
	}
}

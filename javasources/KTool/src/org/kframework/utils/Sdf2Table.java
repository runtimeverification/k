package org.kframework.utils;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;

import org.kframework.utils.file.KPaths;

public class Sdf2Table {

	public static void run_sdf2table(File startDir, String mainFile) {
		ThreadedStreamHandler errorStreamHandler;

		try {
			File f = null;
			String basePath = KPaths.getKBase(false);

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
			errorStreamHandler.join();

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

	public static Thread run_sdf2table_parallel(File startDir, String mainFile) {
		Sdf2Table st = new Sdf2Table();
		Sdf2tableRunner sr = st.new Sdf2tableRunner(startDir, mainFile);

		sr.start();

		return sr;
	}

	private class Sdf2tableRunner extends Thread {
		File startDir;
		String mainFile;

		public Sdf2tableRunner(File startDir, String mainFile) {
			this.startDir = startDir;
			this.mainFile = mainFile;
		}

		public void run() {
			run_sdf2table(startDir, mainFile);
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

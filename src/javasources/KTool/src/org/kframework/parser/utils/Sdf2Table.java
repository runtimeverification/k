package org.kframework.parser.utils;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;

import org.kframework.utils.ThreadedStreamCapturer;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class Sdf2Table {

	public static void run_sdf2table(File startDir, String mainFile) {
		ThreadedStreamCapturer errorStreamHandler;

		try {
			File f = GlobalSettings.getNativeExecutable("sdf2table");

			// create process
			ProcessBuilder pb = new ProcessBuilder(f.getAbsolutePath(), "-c", "-m", mainFile, "-o", mainFile + ".tbl");
			pb.directory(startDir);

			// start sdf2table process
			Process process = pb.start();

			InputStream errorStream = process.getErrorStream();
			// these need to run as java thread to get the standard error from the command.
			errorStreamHandler = new ThreadedStreamCapturer(errorStream);
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

}

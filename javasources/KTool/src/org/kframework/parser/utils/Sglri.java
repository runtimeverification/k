package org.kframework.parser.utils;

import java.io.File;
import java.io.IOException;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.utils.ThreadedStreamCapturer;
import org.kframework.utils.file.KPaths;

import aterm.ATerm;

public class Sglri {

	public static ASTNode run_sglri(String tablePath, String startSymbol, String content) {
		ThreadedStreamCapturer errorStreamHandler;
		ThreadedATermReader inputATermReader;

		try {
			File f = null;
			String basePath = KPaths.getKBase(false);

			if (isUnixOS()) {
				f = new File(basePath + "/bin/native/linux/sglri");
				f.setExecutable(true, false);
			}
			if (isWindowsOS()) {
				f = new File(basePath + "/bin/native/cygwin/sglri.exe");
			}
			if (isMacOS()) {
				f = new File(basePath + "/bin/native/macosx/sglri");
				f.setExecutable(true, false);
			}

			// create process
			ProcessBuilder pb = new ProcessBuilder(f.getAbsolutePath(), "-p", tablePath, "-s", startSymbol, "-b", "--preserve-locations");
			//pb.directory(startDir);

			// start sdf2table process
			Process process = pb.start();

			process.getOutputStream().write(content.getBytes());
			process.getOutputStream().close();
			// these need to run as java thread to get the standard error from the command.
			errorStreamHandler = new ThreadedStreamCapturer(process.getErrorStream());
			inputATermReader = new ThreadedATermReader(process.getInputStream());
			errorStreamHandler.start();
			inputATermReader.start();
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

			inputATermReader.join();
			ATerm atm = inputATermReader.getAterm();
			return JavaClassesFactory.getTerm(atm);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		return null;
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

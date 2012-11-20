package org.kframework.utils.maude;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class MaudeRun {

	static String maudeExe = initializeMaudeExecutable();
	static boolean internalMaude = true;

	/**
	 * This function computes the path to a K-included version of maude. It assumes that /dist/bin/maude directory contains all maude executables. It searches for the os type and the architecture and it returns the right maude executable.
	 */
	public static String initializeMaudeExecutable() {
		if (checkLocalMaudeInstallation()) {
			String msg = "Maude is already installed on this machine. Please remove directory k-install-dir/bin/maude/binaries to use your local maude installation. ";
			GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.INTERNAL, msg, "File System", KPaths.getKBase(false) + "/bin/maude/binaries"));
		}

		// get system properties: file separator, os name, os architecture
		String fileSeparator = System.getProperty("file.separator");
		String osname = System.getProperty("os.name");
        String version = System.getProperty("os.version");
		String arch = System.getProperty("os.arch");

		// set different maude executables
		String maude_win = "maude.exe";
		String maude_mac_leopard = "maude.intelDarwinLeopard";
        String maude_mac = "maude.intelDarwin";
		String maude_linux_32 = "maude.linux";
		String maude_linux_64 = "maude.linux64";

		// System.out.println("OS: |" + osname + "|" + arch + "|");
		// System.out.println(KPaths.getKBase(true));

		String maudeDir = KPaths.getKBase(false) + fileSeparator + "bin" + fileSeparator + "maude" + fileSeparator + "binaries";
		String maudeExe = "maude";


		if (osname.toLowerCase().contains("win")) {
			// silently ignore this case
			// the user should install itself maude
			// we assume that he can execute maude from command line
			maudeExe = maudeDir + fileSeparator + maude_win;
		//} else if (osname.toLowerCase().contains("mac")) {
			// I hope this condition is strong enough
        } else if (osname.equals("Mac OS X")) {
            String subversion = version.substring(3, version.indexOf('.', 3));
            // if at least Snow Leopard
            if (Integer.parseInt(subversion) >= 6)
			    maudeExe = maudeDir + fileSeparator + maude_mac;
            else
                maudeExe = maudeDir + fileSeparator + maude_mac_leopard;
		} else if (osname.toLowerCase().contains("linux")) {
			// in this case we assume linux
			if (arch.toLowerCase().contains("64")) {
				maudeExe = maudeDir + fileSeparator + maude_linux_64;
			} else
				maudeExe = maudeDir + fileSeparator + maude_linux_32;
		}

		final File maude = new File(maudeExe);
		if (!maude.exists()) {
			KException exception = new KException(ExceptionType.WARNING, KExceptionGroup.CRITICAL,
					"Cannot execute Maude from " + maudeExe + ".\n" +
							"Will assume that Maude is installed by the user such that\n" +
							"it can be executed with no warnings using the 'maude' command.",
					"top level", "");
			GlobalSettings.kem.register(exception);
			// if the maude binaries are not found then consider default `maude`
			internalMaude = false;
			return "maude";
		} else {
			if (!maude.canExecute()) {
				maude.setExecutable(true);
			}
		}

		return maudeExe;
	}

	private static boolean checkLocalMaudeInstallation() {
		String localMaude = "maude";

		try {
			java.lang.ProcessBuilder pb = new java.lang.ProcessBuilder(localMaude);
			pb.redirectErrorStream(true);

			Process p = pb.start();

			OutputStream os = p.getOutputStream();
			os.write("q\n".getBytes());
			os.flush();
			os.close();

			InputStream is = p.getInputStream();
			BufferedReader br = new BufferedReader(new InputStreamReader(is));
			String line = "";
			String output = "";
			while ((line = br.readLine()) != null) {
				output += line + "\n";
			}

			p.waitFor();
			if (output.matches("GLIBC")) {
				return false;
			}

			if (output.matches("[Ww]arning")) {
				return false;
			}

			if (output.matches("[Ee]rror")) {
				return false;
			}
		} catch (Exception e) {
			return false;
		}

		return true;
	}

	public static String run_maude(File startDir, String mainFile) {
		try {
			// create process
			java.lang.ProcessBuilder pb = new java.lang.ProcessBuilder();
			List<String> args = new ArrayList<String>();
			args.add(maudeExe);
			args.add("-no-wrap");
			args.add("-no-banner");
			pb.command(args);

			// set execution directory to current user dir
			pb.directory(startDir);

			// set environment variables for this process
			// Map<String, String> environment = pb.environment();
			// environment.put("PATH", System.getenv("PATH"));
			// environment.put("MAUDE_LIB", System.getenv("MAUDE_LIB"));

			// start maude
			Process maude = null;
			try {
				maude = pb.start();
			} catch (IOException e) {
				final String message;
				if (internalMaude) {
					message = "K requires Maude to compile and execute.  Apparently the provided maude executable '" + maudeExe + "'\n" +
							"does not execute correctly.  Please check file permissions.\n" +
							"If you have Maude installed on your machine you could consider removing the '" + maudeExe + "' file to let K" +
							"use the local version.\n";

				} else {
					message = "Cannot execute maude as '" + maudeExe + "'. Please check if maude installed and it is in your PATH.\n" +
							"and that '" + maudeExe + "' executes from command line with no warnings.";
				}
				KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message,
						"top level", "run_maude method");
				GlobalSettings.kem.register(exception);
				return "";
			}

			// capture out and err and store them in corresponding files
			String kompile_out = startDir.getAbsolutePath() + "/kompile_out.txt";
			String kompile_err = startDir.getAbsolutePath() + "/kompile_err.txt";

			StreamCapturer outc = new StreamCapturer(maude.getInputStream(), kompile_out);
			StreamCapturer errc = new StreamCapturer(maude.getErrorStream(), kompile_err);
			outc.start();
			errc.start();

			OutputStream os = maude.getOutputStream();
			try {
				os.write(mainFile.getBytes());
				os.close();
			} catch (IOException e) {
				String message = "The '" + maudeExe + "' process cannot receive input. Please report.";
				KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message,
						"top level", "run_maude method");
				GlobalSettings.kem.register(exception);
			}

			// wait for maude to finish
			maude.waitFor();

			synchronized (outc) {
				if (outc.isAlive())
					outc.wait();
			}
			synchronized (errc) {
				if (errc.isAlive())
					errc.wait();
			}

			String output = outc.output; // FileUtil.getFileContent(kompile_out);
			String error = errc.output; // FileUtil.getFileContent(kompile_err);

			// display both error messages from maude compiler and from maude itself!
			// report:
			// "Maude compiler error: compiler:
			// "Maude error: error"
			if (!output.equals("")) {
				String errSpecificStart = "[ERROR]";
				String errSpecificEnd = "[ENDERROR]";
				int begin = output.indexOf(errSpecificStart);
				if (begin != -1) {
					int end = output.indexOf(errSpecificEnd);
					String message;
					if (end != -1) {
						message = output.substring(begin + errSpecificStart.length(), end);
					} else {
						message = output.substring(begin + errSpecificStart.length());
					}
					KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message,
							"top level", "Maude compilation");
					GlobalSettings.kem.register(exception);
				}
			}
			if (!error.equals("")) {
				FileUtil.saveInFile(kompile_err, error);
				String message;
				if (error.length() > 500) {
					message = error.substring(0, 500) + "...\nCheck " + kompile_err + " to see the complete error.";
				} else {
					message = error;
				}
				KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message,
						"top level", "Maude compilation");
				GlobalSettings.kem.register(exception);
			}

			return output;
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		return "";
	}
}

package k.utils;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStream;

public class MaudeRun {

	public static String run_maude(File startDir, String mainFile) {
		try {
			// create process
			java.lang.ProcessBuilder pb = new java.lang.ProcessBuilder("maude");

			// set execution directory to current user dir
			pb.directory(startDir);

			// set environment variables for this process
			// Map<String, String> environment = pb.environment();
			// environment.put("PATH", System.getenv("PATH"));
			// environment.put("MAUDE_LIB", System.getenv("MAUDE_LIB"));

			// start maude
			Process maude = pb.start();

			// capture out and err and store them in corresponding files
			String kompile_out = startDir.getAbsolutePath() + "/kompile_out.txt";
			String kompile_err = startDir.getAbsolutePath() + "/kompile_err.txt";

			StreamCapturer outc = new StreamCapturer(maude.getInputStream(), kompile_out);
			StreamCapturer errc = new StreamCapturer(maude.getErrorStream(), kompile_err);
			outc.start();
			errc.start();

			OutputStream os = maude.getOutputStream();
			os.write(mainFile.getBytes());
			os.close();

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
				int end = output.indexOf(errSpecificEnd);
				if (begin != -1 && end != -1) {
					System.out.println("Error: " + output.substring(begin + errSpecificStart.length(), end));
					System.exit(1);
				}
			}
			if (!error.equals("")) {
				if (error.length() > 500) {
					FileUtil.saveInFile(kompile_err, error);
					Error.report(error.substring(0, 500) + "...\nCheck " + kompile_err + " to see the complete error.");
				} else {
					FileUtil.saveInFile(kompile_err, error);
					System.out.println("Error: " + error);
					System.exit(1);
				}
			}

			return output;
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		} catch (IOException e) {
			System.out.println("Cannot execute maude. Please check if maude installed and MAUDE_LIB is set.\nIf maude is installed then 'maude' command should execute from command line.");
			System.exit(1);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		return "";
	}
}

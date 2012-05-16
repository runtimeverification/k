package ro.uaic.fmse.jkrun;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Map;

public class Maude {

	public static String run_maude(String... commands) {
		try {

			// set maude input file
			String cmds = "";
			for (String s : commands)
				cmds += s + K.lineSeparator;
			cmds += "q" + K.lineSeparator;
			FileUtil.saveInFile(K.maude_in, cmds);

			// create process
			java.lang.ProcessBuilder pb = new java.lang.ProcessBuilder(K.maude, "-no-banner", "-no-wrap", "-xml-log=xmloutput.txt");

			// set execution directory to current user dir
			pb.directory(new File(K.userdir));

			// set environment variables for this process
			Map<String, String> environment = pb.environment();
			environment.put("PATH", System.getenv("PATH"));
			environment.put("MAUDE_LIB", System.getenv("MAUDE_LIB"));

			// start maude
			Process maude = pb.start();

			// capture out and err and store them in corresponding files
			StreamCapturer outc = new StreamCapturer(maude.getInputStream(), K.maude_out);
			StreamCapturer errc = new StreamCapturer(maude.getErrorStream(), K.maude_err);
			outc.start();
			errc.start();

			// send input and quit
			OutputStream out = maude.getOutputStream();
			out.write(("in " + K.maude_in + " . \n").getBytes());
			out.close();
			// wait for maude to finish
			maude.waitFor();

			Thread.sleep(100); // this should be removed.

			String output = FileUtil.getFileContent(K.maude_out);
			String error = FileUtil.getFileContent(K.maude_err);

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
					Error.report(output.substring(begin + errSpecificStart.length(), end));
				}

			}
			if (!error.equals("")) {
				if (error.length() > 500) {
					FileUtil.saveInFile(K.maude_err, error);
					Error.report(error.substring(0, 500) + "...\nCheck " + K.maude_err + " to see the complete error.");
				} else {
					FileUtil.saveInFile(K.maude_err, error);
					Error.report(error);
				}
			}

			return output;
		} catch (FileNotFoundException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IOException e) {
			System.out.println("Cannot execute maude. Please check if maude installed and MAUDE_LIB is set.\nIf maude is installed then 'maude' command should execute from command line.");
			System.exit(1);
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return "";
	}
}

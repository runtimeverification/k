package ro.uaic.info.fmse.maude;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import ro.uaic.info.fmse.utils.file.FileUtil;

public class StreamCapturer extends Thread {
	InputStream is;
	String outputFile;
	public String output = "";

	// reads everything from is until empty.
	StreamCapturer(InputStream is, String outputFile) {
		this.is = is;
		this.outputFile = outputFile;
	}

	public void run() {
		try {
			InputStreamReader isr = new InputStreamReader(is);
			BufferedReader br = new BufferedReader(isr);
			String line = null;
			while ((line = br.readLine()) != null) {
				output += line + System.getProperty("line.separator");
			}
			FileUtil.saveInFile(outputFile, output);
		} catch (IOException ioe) {
			ioe.printStackTrace();
		}
	}
}

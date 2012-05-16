package ro.uaic.fmse.jkrun;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class StreamCapturer extends Thread {
	InputStream is;
	String outputFile;
	public String output;

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
			String out = "";
			while ((line = br.readLine()) != null) {
				out += line + K.lineSeparator;
			}
			FileUtil.saveInFile(outputFile, out);
		} catch (IOException ioe) {
			ioe.printStackTrace();
		}
	}
}
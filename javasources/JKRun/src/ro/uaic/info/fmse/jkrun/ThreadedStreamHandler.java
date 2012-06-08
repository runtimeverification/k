package ro.uaic.info.fmse.jkrun;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class ThreadedStreamHandler extends Thread {

	InputStream inputStream;
	StringBuilder content = new StringBuilder();

	ThreadedStreamHandler(InputStream inputStream) {
		this.inputStream = inputStream;
	}

	public void run() {
		BufferedReader bufferedReader = null;
		try {
			bufferedReader = new BufferedReader(new InputStreamReader(inputStream));
			String line = null;
			while ((line = bufferedReader.readLine()) != null) {
				content.append(line + K.lineSeparator);
			}
		} catch (IOException ioe) {
			ioe.printStackTrace();
		} catch (Throwable t) {
			t.printStackTrace();
		} finally {
			try {
				bufferedReader.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * @return the content
	 */
	public StringBuilder getContent() {
		return content;
	}
}

package org.kframework.krun;

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
			Error.report("Error while running thread:" + ioe.getMessage());
		} catch (Throwable t) {
			Error.report("Error while running thread:" + t.getMessage());
		} finally {
			try {
				bufferedReader.close();
			} catch (IOException e) {
				Error.report("Error while running thread:" + e.getMessage());
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

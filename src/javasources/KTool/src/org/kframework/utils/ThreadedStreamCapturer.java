// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class ThreadedStreamCapturer extends Thread {

    InputStream inputStream;
    StringBuilder content = new StringBuilder();

    public ThreadedStreamCapturer(InputStream inputStream) {
        this.inputStream = inputStream;
    }

    public void run() {
        String sep = System.getProperty("line.separator");
        try (BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(inputStream))) {
            String line = null;
            while ((line = bufferedReader.readLine()) != null) {
                content.append(line + sep);
            }
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }

    /**
     * @return the content
     */
    public StringBuilder getContent() {
        return content;
    }
}

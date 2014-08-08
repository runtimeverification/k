// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.lang.ProcessBuilder.Redirect;

public class ExternalProcessServer {
    // Generic server process
    private final String executable;
    private Process server;
    private DataOutputStream output;
    private DataInputStream input;

    private final boolean DEBUG = false;

    // A flag signaling whether this is the first time the server process is instantiated.
    private boolean firstTime;

    public ExternalProcessServer(String executable) {
        this.executable = executable;

        server = null;
        output = null;
        input = null;
        firstTime = true;
    }

    /** Start the server process */
    public void init() throws IOException {
        if (!firstTime) return;
        File f = OS.current().getNativeExecutable(executable);

        ProcessBuilder pb = new ProcessBuilder(f.getAbsolutePath());
        pb.redirectError(Redirect.INHERIT);
        server = pb.start();
        output = new DataOutputStream(server.getOutputStream());
        input = new DataInputStream(server.getInputStream());

        Thread childWatcher = new Thread(new Runnable() {
            @Override
            public void run() {
                int exitCode;
                try {
                    exitCode = server.waitFor();
                    if (DEBUG)
                        System.err.println(executable + " server exited with code " + exitCode);
                } catch (InterruptedException e) {
                    if (DEBUG)
                        System.err.println("Interrupted while waiting for " + executable + " server");
                }
            }
        });
        childWatcher.setDaemon(true);
        childWatcher.start();

        firstTime = false;
    }

    /**
     * Send the low-order bytes of the string to the process.
     * @param str
     * @throws java.io.IOException
     */
    public void sendString(String str) throws IOException {
        output.writeInt(str.length());
        if (DEBUG) {
            System.err.println("sent length "+str.length());
        }
        output.writeBytes(str);
        if (DEBUG) {
            System.err.println("sent string "+str);
        }
    }

    /**
     * Receive a response from the process
     * @return
     * @throws java.io.IOException
     */
    public byte[] readBytes() throws IOException {
        int len = input.readInt();
        if (DEBUG) {
            System.err.println("read length "+len);
        }
        byte[] bytes = new byte[len];
        input.readFully(bytes);
        if (DEBUG) {
            System.err.println("got bytes");
        }
        return bytes;
    }

    public void flushOutput() throws IOException {
        output.flush();
    }

    public void destroy() {
        server.destroy();
    }
}

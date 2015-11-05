// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.utils.ThreadedStreamCapturer;
import org.kframework.utils.errorsystem.KEMException;

import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

// instantiate processes
public class RunProcess {

    public static class ProcessOutput {
        public final String stdout;
        public final String stderr;
        public final int exitCode;

        public ProcessOutput(String stdout, String stderr, int exitCode) {
            this.stdout = stdout;
            this.stderr = stderr;
            this.exitCode = exitCode;
        }
    }

    private RunProcess() {}

    public static ProcessOutput execute(Map<String, String> environment, ProcessBuilder pb, String... commands) {

        ThreadedStreamCapturer inputStreamHandler, errorStreamHandler;

        try {
            if (commands.length <= 0) {
                throw KEMException.criticalError("Need command options to run");
            }

            // create process
            pb = pb.command(commands);
            Map<String, String> realEnvironment = pb.environment();
            realEnvironment.putAll(environment);

            // start process
            Process process = pb.start();

            InputStream inputStream = process.getInputStream();
            InputStream errorStream = process.getErrorStream();
            // these need to run as java threads to get the standard output and error from the command.
            inputStreamHandler = new ThreadedStreamCapturer(inputStream);
            errorStreamHandler = new ThreadedStreamCapturer(errorStream);

            inputStreamHandler.start();
            errorStreamHandler.start();

            // wait for process to finish
            process.waitFor();

            synchronized (inputStreamHandler) {
                while (inputStreamHandler.isAlive())
                    inputStreamHandler.wait();
            }
            synchronized (errorStreamHandler) {
                while (errorStreamHandler.isAlive())
                    errorStreamHandler.wait();
            }

            String s1 = inputStreamHandler.getContent().toString();

            String s2 = errorStreamHandler.getContent().toString();

            return new ProcessOutput(s1, s2, process.exitValue());

        } catch (IOException | InterruptedException e) {
            throw KEMException.criticalError("Error while running process:" + e.getMessage(), e);
        }

    }

}

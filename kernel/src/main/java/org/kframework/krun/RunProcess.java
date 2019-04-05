// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.utils.errorsystem.KEMException;

import org.apache.commons.io.IOUtils;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.Map;
import java.util.Scanner;
import java.util.function.Supplier;

// instantiate processes
public class RunProcess {

    /**
     * Returns a thread that pipes all incoming data from {@param in} to {@param out}.
     * @param in A function that returns the input stream to be piped to {@param out}
     * @param out The output stream to pipe data to.
     * @return A {@link Thread} that will pipe all data from {@param in} to {@param out} until EOF is reached.
     */
    public static Thread getOutputStreamThread(Supplier<InputStream> in, PrintStream out) {
        return new Thread(() -> {
                    try {
                        IOUtils.copy(in.get(), out);
                    } catch (IOException e) {}
                });
    }

    public static class ProcessOutput {
        public final byte[] stdout;
        public final byte[] stderr;
        public final int exitCode;

        public ProcessOutput(byte[] stdout, byte[] stderr, int exitCode) {
            this.stdout = stdout;
            this.stderr = stderr;
            this.exitCode = exitCode;
        }
    }

    private RunProcess() {}

    public static ProcessOutput execute(Map<String, String> environment, ProcessBuilder pb, String... commands) {


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

            ByteArrayOutputStream out, err;
            PrintStream outWriter, errWriter;
            out = new ByteArrayOutputStream();
            err = new ByteArrayOutputStream();
            outWriter = new PrintStream(out);
            errWriter = new PrintStream(err);

            Thread outThread = getOutputStreamThread(process::getInputStream, outWriter);
            Thread errThread = getOutputStreamThread(process::getErrorStream, errWriter);

            outThread.start();
            errThread.start();

            // wait for process to finish
            process.waitFor();

            outThread.join();
            errThread.join();
            outWriter.flush();
            errWriter.flush();

            return new ProcessOutput(out.toByteArray(), err.toByteArray(), process.exitValue());

        } catch (IOException | InterruptedException e) {
            throw KEMException.criticalError("Error while running process:" + e.getMessage(), e);
        }

    }

}

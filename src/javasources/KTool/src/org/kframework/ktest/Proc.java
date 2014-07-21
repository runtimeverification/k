// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.apache.commons.io.IOUtils;
import org.kframework.ktest.StringMatcher.MatchFailure;
import org.kframework.krun.ColorSetting;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.awt.*;
import java.io.*;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.*;

/**
 * A unified process class for kompile, kompile --pdf and krun processes.
 */
public class Proc<T> implements Runnable {

    private final String[] args;
    private File workingDir;

    /**
     * Expected program output with location information for output file.
     */
    private final Annotated<String, String> expectedOut;

    /**
     * Output produced by program.
     */
    private String pgmOut;

    /**
     * Expected program error.
     */
    private final Annotated<String, String> expectedErr;

    /**
     * Error produced by program.
     */
    private String pgmErr;

    /**
     * Input string to pass to program.
     */
    private final String procInput;

    /**
     * String to be used while logging the process results.
     */
    private final String logStr;

    /**
     * Comparator to compare program outputs with expected outputs.
     */
    private final StringMatcher strComparator;

    /**
     * Some arbitrary user data to later get with `getObj()'.
     */
    private final T obj;

    /**
     * Timeout for process in milliseconds.
     */
    private final int timeout;

    private final boolean verbose;
    private final ColorSetting colorSetting;
    private final Color terminalColor;

    private final boolean updateOut;
    private final boolean generateOut;
    private final String outputFile;
    private final String newOutputFile;

    /**
     * Whether the process succeeded or not.
     */
    private boolean success = false;

    /**
     * Reason of failure. null if process is not started yet or it's succeeded.
     */
    private String reason = null;

    /**
     * How long did process take.
     */
    private long timeDelta;

    public static final int SIGTERM = 143;

    /**
     *
     * @param obj this is basically an arbitrary object to keep in a process,
     *            this used to know which TestCase a process is running
     * @param args arguments to pass to process
     * @param expectedOut null to ignore the program output, output messages are ignored when
     *                    program fails with an error
     * @param expectedErr null if not testing for error output, error messages are ignored when
     *                    program returns 0
     * @param procInput null or empty string to not pass anything to program input
     * @param strComparator comparator object to compare program outputs with expected outputs
     */
    public Proc(T obj, String[] args, String procInput, Annotated<String, String> expectedOut,
                Annotated<String, String> expectedErr, String logStr,
                StringMatcher strComparator, int timeout, boolean verbose,
                ColorSetting colorSetting, Color terminalColor,
                boolean updateOut, boolean generateOut,
                String outputFile, String newOutputFile) {
        this.obj = obj;
        this.args = args;
        this.expectedOut = expectedOut;
        this.expectedErr = expectedErr;
        this.logStr = logStr;
        this.procInput = procInput;
        this.strComparator = strComparator;
        this.timeout = timeout;
        this.verbose = verbose;
        this.colorSetting = colorSetting;
        this.terminalColor = terminalColor;
        this.updateOut = updateOut;
        this.generateOut = generateOut;
        this.outputFile = outputFile;
        this.newOutputFile = newOutputFile;
    }

    public Proc(T obj, String[] args, String logStr, StringMatcher strComparator, int timeout,
                boolean verbose, ColorSetting colorSetting, Color terminalColor,
                boolean updateOut, boolean generateOut) {
        this(obj, args, "", null, null, logStr, strComparator, timeout, verbose, colorSetting,
            terminalColor, updateOut, generateOut, null, null);
    }

    @Override
    public void run() {
        // TODO: what happens when a process is run multiple times?
        ProcessBuilder pb = new ProcessBuilder(args).directory(workingDir);
        pb.environment().put("kompile", ExecNames.getKompile());
        pb.environment().put("krun", ExecNames.getKrun());
        pb.environment().put("kast", ExecNames.getKast());

        try {
            long startTime = System.currentTimeMillis();
            Process proc = pb.start();

            // I'm using a different naming convention because this is more intuitive for me
            InputStream errorStream = proc.getErrorStream(); // program's error stream
            InputStream outStream = proc.getInputStream(); // program's output stream
            OutputStream inStream = proc.getOutputStream(); // program's input stream

            // pass input to process
            IOUtils.write(procInput, inStream);
            inStream.close();

            // asynchronously read outputs
            final ExecutorService service = Executors.newFixedThreadPool(2);
            final Future<String> outputGobbler = service.submit(new StreamGobbler(outStream));
            final Future<String> errorGobbler  = service.submit(new StreamGobbler(errorStream));

            int returnCode = wait(proc);
            timeDelta = System.currentTimeMillis() - startTime;

            try {
                pgmOut = outputGobbler.get();
                pgmErr = errorGobbler.get();
            } catch (InterruptedException | ExecutionException e) {
                // program was killed before producing output,
                // set pgmOut and pgmErr null manually, in case one of the outputs is produced
                // but other is not (not sure if that's possible, just to make sure..)
                pgmOut = null;
                pgmErr = null;
            }

            handlePgmResult(returnCode);
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.WARNING,
                            KException.KExceptionGroup.INTERNAL, e.getMessage(), "command line",
                            "System file."));
            reportErr("program failed with exception: " + e.getMessage());
        }
    }

    /**
     * @return true if process finished with success.
     */
    public boolean isSuccess() {
        return success;
    }

    public T getObj() {
        return obj;
    }

    /**
     * @return reason of failure. null when process is not started yet or it's succeeded.
     */
    public String getReason() {
        return reason;
    }

    public long getTimeDelta() {
        return timeDelta;
    }

    /**
     * @return Program output. null when proces is not started yet or it's failed before
     *         producing output (i.e. when killed because of timeout)
     */
    public String getPgmOut() {
        return pgmOut;
    }

    /**
     * @return Program error output. null when proces is not started yet or it's failed before
     *         producing error output (i.e. when killed because of timeout)
     */
    public String getPgmErr() {
        return pgmErr;
    }

    public File getWorkingDir() {
        return workingDir;
    }

    public void setWorkingDir(File workingDir) {
        this.workingDir = workingDir;
    }

    private int wait(final Process proc) throws InterruptedException {
        Timer timer = new Timer();
        timer.schedule(new TimerTask() {
            @Override
            public void run() {
                proc.destroy();
            }
        }, timeout);
        int ret = proc.waitFor();
        timer.cancel();
        return ret;
    }

    /**
     * Compare expected outputs with program outputs, set `reason' and `success' variables,
     * print information messages.
     * @param returnCode return code of the process
     */
    private void handlePgmResult(int returnCode) throws IOException {
        String red = ColorUtil.RgbToAnsi(Color.RED, colorSetting, terminalColor);
        if (returnCode == 0) {

            boolean doGenerateOut = false;

            // program ended successfully ..
            if (expectedOut == null) {
                // we're not comparing outputs
                success = true;
                if (verbose)
                    System.out.format("Done with [%s] (time %d ms)%n", logStr, timeDelta);
                doGenerateOut = true;
            } else {
                try {
                    strComparator.matches(expectedOut.getObj(), pgmOut);

                    // outputs match
                    success = true;
                    if (verbose)
                        System.out.format("Done with [%s] (time %d ms)%n", logStr, timeDelta);
                } catch (MatchFailure e) {
                    // outputs don't match
                    System.out.format(
                            "%sERROR: [%s] output doesn't match with expected output (time: %d ms)%s%n",
                            red, logStr, timeDelta, ColorUtil.ANSI_NORMAL);
                    reportOutMatch(e.getMessage());
                    if (verbose)
                        System.out.println(getReason());
                    doGenerateOut = true;
                }
            }

            if (updateOut && outputFile != null) {
                IOUtils.write(pgmOut, new FileOutputStream(new File(outputFile)));
                System.out.println("Updating output file: " + outputFile);
            }
            if (doGenerateOut && generateOut && newOutputFile != null) {
                IOUtils.write(pgmOut, new FileOutputStream(new File(newOutputFile)));
                System.out.println("Generating output file: " + newOutputFile);
            }

        } else if (returnCode == SIGTERM) {

            // TODO: is it possible for program to be killed because of something other than
            //       timeout? (full memory etc.)
            System.out.format("%sERROR: [%s] killed due to timeout.%s%n",
                    red, logStr, ColorUtil.ANSI_NORMAL);
            reportTimeout();

        } else {

            // program ended with error ..
            if (expectedErr == null) {
                // we're not comparing error outputs
                System.out.format("%sERROR: [%s] failed with error (time: %d ms)%s%n",
                        red, logStr, timeDelta, ColorUtil.ANSI_NORMAL);
                if (verbose)
                    System.out.format("error was: %s%n", pgmErr);
                reportErr(pgmErr);
            } else {
                try {
                    strComparator.matches(expectedErr.getObj(), pgmErr);
                    // error outputs match
                    success = true;
                    if (verbose)
                        System.out.format("Done with [%s] (time %d ms)%n", logStr, timeDelta);
                } catch (MatchFailure e) {
                    // error outputs don't match
                    System.out.format(
                            "%sERROR: [%s] throwed error, but expected error message doesn't match "+
                                    "(time: %d ms)%s%n", red, logStr, timeDelta, ColorUtil.ANSI_NORMAL);
                    reportErrMatch(e.getMessage());
                }
            }
        }
    }

    private void reportErr(String err) {
        assert reason == null;
        reason = err;
    }

    private void reportErrMatch(String message) {
        assert reason == null;
        reason = "Unexpected program error:\n" + message;
    }

    private void reportOutMatch(String message) {
        assert reason == null;
        reason = "Unexpected program output:\n" + message;
    }

    private void reportTimeout() {
        assert reason == null;
        reason = "Timeout";
    }
}

class StreamGobbler implements Callable<String> {
    InputStream is;

    StreamGobbler(InputStream is) {
        this.is = is;
    }

    public String call() throws IOException {
        return IOUtils.toString(is);
    }
}

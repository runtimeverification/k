package org.kframework.ktest2;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.StringUtils;
import org.kframework.krun.ColorSetting;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.awt.*;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Comparator;

/**
 * A unified process class for kompile, kompile --pdf and krun processes.
 */
public class Proc<T> implements Runnable {

    private final String[] args;

    /**
     * Expected program output.
     */
    private final String expectedOut;

    /**
     * Expected program error.
     */
    private final String expectedErr;

    /**
     * Input string to pass to program.
     */
    private final String procInput;

    /**
     * Comparator to compare program outputs with expected outputs.
     */
    private final Comparator<String> strComparator;

    /**
     * Proccess object for internal use.
     */
    private Process proc = null;

    /**
     * Some arbitrary user data to later get with `getObj()'.
     */
    private final T obj;

    private final int timeout;
    private final boolean verbose;
    private final ColorSetting colorSetting;

    /**
     * Whether the process succeeded or not.
     */
    private boolean success = false;

    /**
     * Reason of failure. null if process is not started yet or it's succeeded.
     */
    private String reason = null;

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
    public Proc(T obj, String[] args, String procInput, String expectedOut, String expectedErr,
                Comparator<String> strComparator, int timeout, boolean verbose,
                ColorSetting colorSetting) {
        this.obj = obj;
        this.args = args;
        this.expectedOut = expectedOut;
        this.expectedErr = expectedErr;
        this.procInput = procInput;
        this.strComparator = strComparator;
        this.timeout = timeout;
        this.verbose = verbose;
        this.colorSetting = colorSetting;
    }

    public Proc(T obj, String[] args, int timeout, boolean verbose, ColorSetting colorSetting) {
        this(obj, args, "", "", "", new DefaultStringComparator(), timeout, verbose, colorSetting);
    }

    @Override
    public void run() {
        ProcessBuilder pb = new ProcessBuilder(args);

        try {
            long startTime = System.currentTimeMillis();
            proc = pb.start();

            // I'm using a different naming convention because this is more intuitive for me
            InputStream errorStream = proc.getErrorStream(); // program's error stream
            InputStream outStream = proc.getInputStream(); // program's output stream
            OutputStream inStream = proc.getOutputStream(); // program's input stream

            // pass input to process
            IOUtils.write(procInput, inStream);
            inStream.close();

            int returnCode = proc.waitFor();
            long timeDelta = System.currentTimeMillis() - startTime;

            String pgmOut = IOUtils.toString(outStream);
            String pgmErr = IOUtils.toString(errorStream);

            handlePgmResult(returnCode, pgmOut, pgmErr, timeDelta);
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.WARNING,
                            KException.KExceptionGroup.INTERNAL, e.getMessage(), "command line",
                            "System file."));
            reportErr("program failed with exception: " + e.getMessage());
        }
        proc = null;
    }

    /**
     * Kill spawned process. If no process is spawned or spawned process is ended, nothing happens.
     */
    public void kill() {
        if (proc != null) {
            proc.destroy();
            String procCmd = StringUtils.join(args, ' ');
            GlobalSettings.kem.register(new KException(KException.ExceptionType.WARNING,
                    KException.KExceptionGroup.INTERNAL, procCmd + " is killed", "command line",
                    "System file."));
            success = false;
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

    /**
     * Compare expected outputs with program outputs, set `reason' and `success' variables,
     * print information messages.
     * @param returnCode return code of the process
     * @param pgmOut process output string
     * @param pgmErr process error string
     * @param timeDelta process time
     */
    private void handlePgmResult(int returnCode, String pgmOut, String pgmErr, long timeDelta) {
        String procCmd = StringUtils.join(args, ' ');
        String red = ColorUtil.RgbToAnsi(Color.RED, colorSetting);
        if (returnCode == 0) {

            // program ended successfully ..
            if (expectedOut == null) {
                // we're not comparing outputs
                success = true;
                if (verbose)
                    System.out.format("DONE: %s (time %d ms)%n", procCmd, timeDelta);
            } else if (strComparator.compare(pgmOut, expectedOut) != 0) {
                // outputs don't match
                System.out.format(
                        "%sERROR: %s output doesn't match with expected output (time: %d ms)%s%n",
                        red, procCmd, timeDelta, ColorUtil.ANSI_NORMAL);
                reportOutMatch(expectedOut, pgmOut);
            }
            else {
                // outputs match
                success = true;
                if (verbose)
                    System.out.format("DONE: %s (time %d ms)%n", procCmd, timeDelta);
            }

        } else {

            // program ended with error ..
            if (expectedErr == null) {
                // we're not comparing error outputs
                System.out.format("%sERROR: %s failed with error (time: %d ms)%s%n",
                        red, procCmd, timeDelta, ColorUtil.ANSI_NORMAL);
                reportErr(pgmErr);
            }
            else if (strComparator.compare(pgmErr, expectedErr) == 0) {
                // error outputs match
                success = true;
                if (verbose)
                    System.out.format("DONE: %s (time %d ms)%n", procCmd, timeDelta);
            }
            else {
                // error outputs don't match
                System.out.format(
                        "%sERROR: %s throwed error, but expected error message doesn't match "+
                                "(time: %d ms)%s%n", red, procCmd, timeDelta, ColorUtil.ANSI_NORMAL);
                reportErrMatch(expectedErr, pgmErr);
            }
        }
    }

    private void reportErr(String err) {
        assert reason == null;
        reason = err;
    }

    private void reportErrMatch(String expected, String found) {
        assert reason == null;
        reason = String.format("Expected program error:%n%s%n%nbut found:%n%s%n", expected, found);
    }

    private void reportOutMatch(String expected, String found) {
        assert reason == null;
        reason = String.format("Expected program output:%n%s%n%nbut found:%n%s%n", expected, found);
    }
}

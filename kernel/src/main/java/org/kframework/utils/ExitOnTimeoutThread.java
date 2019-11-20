package org.kframework.utils;

import javax.annotation.Nullable;

/**
 * A daemon thread that awaits given timeout, then exits Java process.
 *
 * @author Denis Bogdanas
 * Created on 30-Oct-19.
 */
public class ExitOnTimeoutThread extends Thread {
    private final Thread thread;
    private final long timeoutMillis;

    /**
     * If {@code specified} is specified, interrupt this thread on timeout. Otherwise call {@code System.exit()}
     */
    public ExitOnTimeoutThread(@Nullable Thread thread, long timeoutMillis) {
        this.thread = thread;
        this.timeoutMillis = timeoutMillis;
        setDaemon(true);
    }

    @Override
    public void run() {
        try {
            if (thread != null) {
                thread.join(timeoutMillis);
                System.err.println("K thread timeout...");
                System.exit(124);
            } else {
                Thread.sleep(timeoutMillis);
                System.err.println("K process timeout...");
                System.exit(124); //bash timeout exit code is 124
            }
        } catch (InterruptedException e) {
            //normal termination, ignoring
        }
    }
}

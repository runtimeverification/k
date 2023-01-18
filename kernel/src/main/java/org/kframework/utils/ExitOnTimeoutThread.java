// Copyright (c) K Team. All Rights Reserved.
package org.kframework.utils;

/**
 * A daemon thread that awaits given timeout, then exits Java process.
 *
 * @author Denis Bogdanas
 * Created on 30-Oct-19.
 */
public class ExitOnTimeoutThread extends Thread {
    private final long timeoutMillis;

    public ExitOnTimeoutThread(long timeoutMillis) {
        this.timeoutMillis = timeoutMillis;
        setDaemon(true);
    }

    @Override
    public void run() {
        try {
            Thread.sleep(timeoutMillis);
            System.err.println("K process timeout...");
            System.exit(124); //bash timeout exit code is 124
        } catch (InterruptedException e) {
            //normal termination, ignoring
        }
    }
}

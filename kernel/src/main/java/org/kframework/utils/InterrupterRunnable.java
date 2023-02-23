// Copyright (c) K Team. All Rights Reserved.
package org.kframework.utils;

/**
 * A runnable that interrupts the given thread when invoked, then awaits termination for the given wait time, in ms.
 *
 * @author Denis Bogdanas
 * Created on 24-Dec-18.
 */
public class InterrupterRunnable implements Runnable {

    private final Thread thread;
    private final long waitTimeMillis;

    public InterrupterRunnable(Thread thread, long waitTimeMillis) {
        this.thread = thread;
        this.waitTimeMillis = waitTimeMillis;
    }

    @Override
    public void run() {
        thread.interrupt();
        try {
            thread.join(waitTimeMillis);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }
}

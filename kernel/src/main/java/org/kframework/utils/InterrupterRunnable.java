// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.utils;

/**
 * A runnable that interrupts the given thread when invoked, then awaits termination for the given wait time, in ms.
 *
 * @author Denis Bogdanas
 * Created on 24-Dec-18.
 */
public class InterrupterRunnable implements Runnable {

    private final Thread thread;
    private final int waitTime;

    public InterrupterRunnable(Thread thread, int waitTime) {
        this.thread = thread;
        this.waitTime = waitTime;
    }

    @Override
    public void run() {
        thread.interrupt();
        try {
            thread.join(waitTime);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }
}

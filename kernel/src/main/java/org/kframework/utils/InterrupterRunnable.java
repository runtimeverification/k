// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.utils;

/**
 * A runnable that interrupts the given thread when invoked, then awaits termination for 5s.
 *
 * @author Denis Bogdanas
 * Created on 24-Dec-18.
 */
public class InterrupterRunnable implements Runnable {

    private Thread thread;

    public InterrupterRunnable(Thread thread) {
        this.thread = thread;
    }

    @Override
    public void run() {
        thread.interrupt();
        try {
            thread.join(5000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }
}

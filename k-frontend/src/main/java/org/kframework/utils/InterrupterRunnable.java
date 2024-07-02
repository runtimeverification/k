// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils;

/**
 * A runnable that interrupts the given thread when invoked, then awaits termination for the given
 * wait time, in ms.
 *
 * @author Denis Bogdanas Created on 24-Dec-18.
 */
public record InterrupterRunnable(Thread thread, long waitTimeMillis) implements Runnable {

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

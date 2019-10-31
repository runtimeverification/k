// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.main;

import org.kframework.utils.inject.RequestScoped;

/**
 * @author Denis Bogdanas
 * Created on 27-Jul-18.
 */
@RequestScoped
public class StartTimeHolder {
    private long startTimeNano = System.nanoTime();

    public long getStartTimeNano() {
        return startTimeNano;
    }

    public static final StartTimeHolder instance = new StartTimeHolder();

    public static void log(String msg) {
        long timeSinceStart = System.nanoTime() - instance.getStartTimeNano();
        System.err.format("%s: %.3f\n", msg, timeSinceStart / 1000000000D);
    }
}

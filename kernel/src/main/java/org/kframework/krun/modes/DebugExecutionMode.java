// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import org.kframework.ExecutionMode;
import org.kframework.Rewriter;
import org.kframework.kore.K;

/**
 * Created by manasvi on 6/10/15.
 */
public class DebugExecutionMode implements ExecutionMode<Void> {
    @Override
    public Void execute(K k, Rewriter rewriter) {
        System.out.println("Kore Debugger Under Construction.");

        return null;
    }
}

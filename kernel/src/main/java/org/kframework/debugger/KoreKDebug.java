// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.Rewriter;
import org.kframework.kore.K;

import java.util.Set;
import java.util.TreeSet;

/**
 * Kore Based Debugger Implementation.
 */
public class KoreKDebug implements KDebug {

    private final int DEFAULT_ID = 0;
    private final int DEFAULT_CHECKPOINT_SIZE = 50;

    private Set<KDebugState> stateSet;
    private KDebugState activeState;
    private Rewriter rewriter;
    private int checkpointSize;

    @Override
    public int step(int steps) {
        return 0;
    }

    public void setCheckpointSize(int checkpointSize) {
        this.checkpointSize = checkpointSize;
    }

    public KoreKDebug(K initialK, Rewriter rewriter) {
        this.stateSet = new TreeSet<>();
        this.checkpointSize = DEFAULT_CHECKPOINT_SIZE;
        KDebugState initialState = new KDebugState();
        initialState.addCheckpoint(new Checkpoint(initialK, DEFAULT_ID), DEFAULT_ID);

    }
}

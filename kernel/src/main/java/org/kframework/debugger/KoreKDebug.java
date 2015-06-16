// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.Rewriter;
import org.kframework.kore.K;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

/**
 * Kore Based Debugger Implementation.
 */
public class KoreKDebug implements KDebug {

    private final int DEFAULT_ID = 1;
    private final int DEFAULT_CHECKPOINT_SIZE = 49;

    private Set<KDebugState> stateSet;
    private KDebugState activeState;
    private Rewriter rewriter;
    private int checkpointInterval;
    private KExceptionManager kem;

    public KoreKDebug(K initialK, Rewriter rewriter, KExceptionManager kem) {
        this.stateSet = new TreeSet<>();
        this.checkpointInterval = DEFAULT_CHECKPOINT_SIZE;
        this.rewriter = rewriter;
        this.kem = kem;
        KDebugState initialState = new KDebugState(initialK);
        initialState.addCheckpoint(new Checkpoint(initialK, DEFAULT_ID), DEFAULT_ID);
        stateSet.add(initialState);
        activeState = initialState;
    }

    @Override
    public int step(int steps) {
        K currentK = activeState.getCurrentK();
        int activeStateCheckpoint = activeState.getActiveStateId();
        if (activeStateCheckpoint != 1 && activeStateCheckpoint % checkpointInterval != 0) {
            if (activeStateCheckpoint + steps < activeState.getlastMapCheckpoint() + checkpointInterval) {
                currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
                activeStateCheckpoint += steps;
                return activeStateCheckpoint;
            }
            currentK = rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval - steps)));
            activeStateCheckpoint += checkpointInterval - steps;
        }
        while (steps >= checkpointInterval) {
            activeStateCheckpoint += checkpointInterval;
            Checkpoint newCheckpoint = new Checkpoint(rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval))),
                    activeStateCheckpoint);
            steps -= checkpointInterval;
            activeState.addCheckpoint(newCheckpoint, activeStateCheckpoint);
            currentK = newCheckpoint.getCheckpointK();
        }
        currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
        activeStateCheckpoint += steps;
        activeState.setCurrentK(currentK);
        return activeStateCheckpoint;
    }

    @Override
    public void setCheckpointInterval(int checkpointInterval) {
        this.checkpointInterval = checkpointInterval;
    }


}

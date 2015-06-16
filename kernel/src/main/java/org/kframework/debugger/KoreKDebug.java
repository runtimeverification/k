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
    private int activeStateCheckpoint;
    public KoreKDebug(K initialK, Rewriter rewriter, KExceptionManager kem) {
        this.stateSet = new TreeSet<>();
        this.checkpointInterval = DEFAULT_CHECKPOINT_SIZE;
        this.rewriter = rewriter;
        this.kem = kem;
        this.activeStateCheckpoint = DEFAULT_ID;
        KDebugState initialState = new KDebugState(initialK);
        initialState.addCheckpoint(new Checkpoint(initialK, DEFAULT_ID), DEFAULT_ID);
        stateSet.add(initialState);
        activeState = initialState;
    }

    @Override
    public int step(int steps) {
        K currentK = activeState.getCurrentK();
        if(activeStateCheckpoint != 1 && activeStateCheckpoint % checkpointInterval != 0) {
            if (activeStateCheckpoint + steps < activeState.getlastMapCheckpoint() + checkpointInterval) {
                currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
                activeStateCheckpoint += steps;
                return activeStateCheckpoint;
            }
            currentK = rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval - steps)));
            activeStateCheckpoint += checkpointInterval - steps;
        }
        currentK = activeState.getCurrentK();
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

    public void setCheckpointInterval(int checkpointSize) {
        this.checkpointInterval = checkpointSize;
    }

    @Override
    public int backStep(int steps) {

    }


}

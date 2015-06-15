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
    private int activeStateId;
    public KoreKDebug(K initialK, Rewriter rewriter, KExceptionManager kem) {
        this.stateSet = new TreeSet<>();
        this.checkpointInterval = DEFAULT_CHECKPOINT_SIZE;
        this.rewriter = rewriter;
        this.kem = kem;
        this.activeStateId = DEFAULT_ID;
        KDebugState initialState = new KDebugState(initialK);
        initialState.addCheckpoint(new Checkpoint(initialK, DEFAULT_ID), DEFAULT_ID);
        stateSet.add(initialState);
        activeState = initialState;
    }

    @Override
    public int step(int steps) {
        K currentK = activeState.getCurrentK();
        if(activeStateId != 1 && activeStateId % checkpointInterval != 0) {
            if (activeStateId + steps < activeState.getCurrentCheckpoint() + checkpointInterval) {
                currentK = rewriter.execute(currentK, Optional.of(new Integer(steps));

            }
        }

        int rollingCheckpointID = activeState.getCurrentCheckpoint();
        currentK = activeState.getCurrentK();
        while (steps >= checkpointInterval) {
            rollingCheckpointID += checkpointInterval;
            Checkpoint newCheckpoint = new Checkpoint(rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval))),
                    rollingCheckpointID);
            steps -= checkpointInterval;
            activeState.addCheckpoint(newCheckpoint, rollingCheckpointID);
            currentK = newCheckpoint.getCheckpointK();
        }


    }

    public void setCheckpointInterval(int checkpointSize) {
        this.checkpointInterval = checkpointSize;
    }


}

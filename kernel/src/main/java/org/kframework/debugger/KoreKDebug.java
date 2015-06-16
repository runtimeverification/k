// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.Rewriter;
import org.kframework.kore.K;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * Kore Based Debugger Implementation.
 */
public class KoreKDebug implements KDebug {

    private final int DEFAULT_ID = 0;
    private final int DEFAULT_CHECKPOINT_SIZE = 50;

    private Set<KDebugState> stateSet;
    private KDebugState activeState;
    private Rewriter rewriter;
    private int checkpointInterval;


    /**
     * Start a Debugger Session. The initial Configuration becomes a part of the new and only state of the Debugger
     *
     * @param initialK The initial Configuration.
     * @param rewriter The Rewriter being used
     * @param kem
     */
    public KoreKDebug(K initialK, Rewriter rewriter) {
        this.stateSet = new HashSet<>();
        this.checkpointInterval = DEFAULT_CHECKPOINT_SIZE;
        this.rewriter = rewriter;
        KDebugState initialState = new KDebugState(initialK);
        initialState.addCheckpoint(new Checkpoint(initialK, DEFAULT_ID), DEFAULT_ID);
        stateSet.add(initialState);
        activeState = initialState;
    }

    @Override
    public KDebugOpResult step(int steps) {
        System.out.println(steps);
        K currentK = activeState.getCurrentK();
        int activeStateCheckpoint = activeState.getActiveStateId();
        if (activeStateCheckpoint % checkpointInterval != 0) {
            if (activeStateCheckpoint + steps < activeState.getlastMapCheckpoint() + checkpointInterval) {
                currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
                activeStateCheckpoint += steps;
                activeState.setActiveStateId(activeStateCheckpoint);
                activeState.setCurrentK(currentK);
                return new KDebugOpResult(currentK, null);
            }
            /* Move to the next Checkpoint */
            currentK = rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval - steps)));
            activeStateCheckpoint += checkpointInterval - steps;
            activeState.addCheckpoint(new Checkpoint(currentK, activeStateCheckpoint), activeStateCheckpoint);
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
        activeState.setActiveStateId(activeStateCheckpoint);
        return new KDebugOpResult(currentK, null);
    }

    @Override
    public void setCheckpointInterval(int checkpointInterval) {
        this.checkpointInterval = checkpointInterval;
    }

    @Override
    public int backStep(int steps) {
        return 0;
    }
}

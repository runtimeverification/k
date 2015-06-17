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

    private Set<DebuggerState> stateSet;
    private DebuggerState activeState;
    private Rewriter rewriter;
    private int checkpointInterval;


    /**
     * Start a Debugger Session. The initial Configuration becomes a part of the new and only state of the Debugger
     *
     * @param initialK The initial Configuration.
     * @param rewriter The Rewriter being used.
     */
    public KoreKDebug(K initialK, Rewriter rewriter) {
        this.stateSet = new HashSet<>();
        this.checkpointInterval = DEFAULT_CHECKPOINT_SIZE;
        this.rewriter = rewriter;
        DebuggerState initialState = new DebuggerState(initialK);
        initialState.addCheckpoint(new RewriterCheckpoint(initialK), DEFAULT_ID);
        stateSet.add(initialState);
        activeState = initialState;
    }

    @Override
    public DebuggerState step(int steps) {
        K currentK = activeState.getCurrentK();
        int activeStateCheckpoint = activeState.getActiveStateId();
        int lastCheckpoint = activeState.getlastMapCheckpoint();

        /* Not enough steps for a new checkpoint */
        if (activeStateCheckpoint + steps < activeState.getlastMapCheckpoint() + checkpointInterval) {
            currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
            activeStateCheckpoint += steps;
            activeState.setActiveStateId(activeStateCheckpoint);
            activeState.setCurrentK(currentK);
            return activeState;
        }
        /* Move to the next Checkpoint */
        currentK = rewriter.execute(currentK, Optional.of(new Integer(lastCheckpoint + checkpointInterval - activeStateCheckpoint)));
        steps -= lastCheckpoint + checkpointInterval - activeStateCheckpoint;
        activeStateCheckpoint = lastCheckpoint + checkpointInterval;
        activeState.addCheckpoint(new RewriterCheckpoint(currentK), activeStateCheckpoint);

        /* Register Checkpoints and Proceed. Take Jumps equal to the Checkpoint Interval */
        while (steps >= checkpointInterval) {
            activeStateCheckpoint += checkpointInterval;
            RewriterCheckpoint newCheckpoint = new RewriterCheckpoint(rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval)))
            );
            steps -= checkpointInterval;
            activeState.addCheckpoint(newCheckpoint, activeStateCheckpoint);
            currentK = newCheckpoint.getCheckpointK();
        }

        /* Final remaining steps */
        currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
        activeStateCheckpoint += steps;
        activeState.setCurrentK(currentK);
        activeState.setActiveStateId(activeStateCheckpoint);
        return activeState;
    }

    @Override
    public void setCheckpointInterval(int checkpointInterval) {
        this.checkpointInterval = checkpointInterval;
    }

    @Override
    public DebuggerState select(int steps) {
        return null;
    }
}

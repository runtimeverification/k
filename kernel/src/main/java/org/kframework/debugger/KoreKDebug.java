// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.Rewriter;
import org.kframework.kore.K;
import org.kframework.krun.tools.Debugger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.NavigableMap;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;

/**
 * Kore Based Debugger Implementation.
 */
public class KoreKDebug implements KDebug {

    private final int DEFAULT_ID = 0;
    private final int DEFAULT_CHECKPOINT_SIZE = 50;

    private List<DebuggerState> stateList;
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
        this.stateList = new ArrayList<>();
        this.checkpointInterval = DEFAULT_CHECKPOINT_SIZE;
        this.rewriter = rewriter;
        NavigableMap<Integer, RewriterCheckpoint> checkpointMap = new TreeMap<>();
        checkpointMap.put(DEFAULT_ID, new RewriterCheckpoint(initialK));
        DebuggerState initialState = new DebuggerState(initialK, DEFAULT_ID, checkpointMap);
        initialState.addCheckpoint(new RewriterCheckpoint(initialK), DEFAULT_ID);
        stateList.add(initialState);
        activeState = initialState;
    }

    @Override
    public DebuggerState step(int steps) {
        K currentK = activeState.getCurrentK();
        int activeStateCheckpoint = activeState.getActiveStateId();
        int lastCheckpoint = activeState.getlastMapCheckpoint();
        DebuggerState nextActiveState;
        stateList.remove(activeState);
        /* Not enough steps for a new checkpoint */
        if (activeStateCheckpoint + steps < activeState.getlastMapCheckpoint() + checkpointInterval) {
            currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
            activeStateCheckpoint += steps;
            NavigableMap<Integer, RewriterCheckpoint> checkpointMap = activeState.getCheckpointMap();
            nextActiveState = new DebuggerState(currentK, activeStateCheckpoint, checkpointMap);
            stateList.add(nextActiveState);
            activeState = nextActiveState;
            return nextActiveState;
        }
        /* Move to the next Checkpoint */
        currentK = rewriter.execute(currentK, Optional.of(new Integer(lastCheckpoint + checkpointInterval - activeStateCheckpoint)));
        NavigableMap<Integer, RewriterCheckpoint> checkpointMap = activeState.getCheckpointMap();
        steps -= lastCheckpoint + checkpointInterval - activeStateCheckpoint;
        activeStateCheckpoint = lastCheckpoint + checkpointInterval;
        checkpointMap.put(new Integer(activeStateCheckpoint), new RewriterCheckpoint(currentK));

        /* Register Checkpoints and Proceed. Take Jumps equal to the Checkpoint Interval */
        while (steps >= checkpointInterval) {
            activeStateCheckpoint += checkpointInterval;
            RewriterCheckpoint newCheckpoint = new RewriterCheckpoint(rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval))));
            steps -= checkpointInterval;
            checkpointMap.put(new Integer(activeStateCheckpoint), newCheckpoint);
            currentK = newCheckpoint.getCheckpointK();
        }

        /* Final remaining steps */
        currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
        activeStateCheckpoint += steps;
        nextActiveState = new DebuggerState(currentK, activeStateCheckpoint, checkpointMap);
        activeState = nextActiveState;
        return nextActiveState;
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

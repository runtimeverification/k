// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;

import org.kframework.kore.K;
import org.kframework.krun.tools.Debugger;

import java.util.NavigableMap;
import java.util.TreeMap;

/**
 * Created by Manasvi on 6/15/15.
 * <p>
 * Class Representing the State of the Debugger.
 * The Debugger can have multiple states at the same time,
 * but only one state is active.
 * <p>
 * Every State has a Checkpoint Enabled History.
 * <p>
 * A State essentially represents a specific branch in the
 * execution tree of a program.
 */
public class DebuggerState {

    private NavigableMap<Integer, RewriterCheckpoint> checkpointMap;

    private K currentK;

    private int stepNum;

    public int getStepNum() {
        return stepNum;
    }

    public void setStepNum(int stepNum) {
        this.stepNum = stepNum;
    }

    public DebuggerState(K currentK, int stepNum, NavigableMap<Integer, RewriterCheckpoint> checkpointMap) {
        this.checkpointMap = new TreeMap<>(checkpointMap);
        this.currentK = currentK;
        this.stepNum = stepNum;
    }

    public DebuggerState(DebuggerState copyState) {
        this.checkpointMap = new TreeMap<>(copyState.getCheckpointMap());
        this.currentK = copyState.getCurrentK();
        this.stepNum = copyState.getStepNum();

    }

    public K getCurrentK() {
        return currentK;
    }


    /**
     * Get the last checkpoint from the Map.
     * The last checkpoint may not have the most recent K.
     *
     * @return The most recent checkpoint element in the Map
     */
    public int getlastMapCheckpoint() {
        return checkpointMap.lastKey();
    }

    public NavigableMap<Integer, RewriterCheckpoint> getCheckpointMap() {
        return new TreeMap<>(checkpointMap);
    }
}

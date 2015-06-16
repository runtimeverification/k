// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;

import org.kframework.kore.K;

import java.util.NavigableMap;
import java.util.TreeMap;

/**
 * Created by Manasvi on 6/15/15.
 *
 * Class Representing the State of the Debugger.
 * The Debugger can have multiple states at the same time,
 * but only one state is active.
 *
 * Every State has a Checkpoint Enabled History.
 *
 * A State essentially represents a specific branch in the
 * execution tree of a program.
 *
 */
public class KDebugState {

    private NavigableMap<Integer, Checkpoint> checkpointMap;

    private K currentK;

    public int getActiveStateId() {
        return activeStateId;
    }

    public void setActiveStateId(int activeStateId) {
        this.activeStateId = activeStateId;
    }

    private int activeStateId;

    public KDebugState(K initialK) {
        checkpointMap = new TreeMap<>();
        currentK = initialK;
    }

    public void addCheckpoint(Checkpoint checkpoint, int checkpointNum) {
        checkpointMap.put(checkpointNum, checkpoint);
    }

    public K getCurrentK() {
        return currentK;
    }

    public void setCurrentK(K currentK) {
        this.currentK = currentK;
    }

    /**
     * Get the last checkpoint from the Map.
     * The last checkpoint may not have the most recent K.
     *
     * @return The most recent checkpoint element in the Map

     */
    public Integer getlastMapCheckpoint() {
        return checkpointMap.lastKey();
    }
}

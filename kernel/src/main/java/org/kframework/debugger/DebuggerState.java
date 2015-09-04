// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;

import com.google.common.collect.Maps;
import org.kframework.kore.K;
import org.kframework.krun.tools.Debugger;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
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

    private final NavigableMap<Integer, K> checkpointMap;

    private final List<DebuggerMatchResult> watchList;

    private final K currentK;

    private final int stepNum;

    public DebuggerState(K currentK, int stepNum, NavigableMap<Integer, K> checkpointMap, List<DebuggerMatchResult> watchList) {
        this.checkpointMap = new TreeMap<>(checkpointMap);
        this.watchList = new ArrayList<>(watchList);
        this.currentK = currentK;
        this.stepNum = stepNum;
    }

    public DebuggerState(DebuggerState copyState) {
        this.checkpointMap = new TreeMap<>(copyState.getCheckpointMap());
        this.watchList = new ArrayList<>(copyState.getWatchList());
        this.currentK = copyState.getCurrentK();
        this.stepNum = copyState.getStepNum();
    }

    public K getCurrentK() {
        return currentK;
    }

    public int getStepNum() {
        return stepNum;
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

    public List<DebuggerMatchResult> getWatchList() {
        return Collections.unmodifiableList(watchList);
    }

    public NavigableMap<Integer, K> getCheckpointMap() {
        return Maps.unmodifiableNavigableMap(checkpointMap);
    }
}

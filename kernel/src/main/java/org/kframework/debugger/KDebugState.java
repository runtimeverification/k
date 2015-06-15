// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;

import java.util.NavigableMap;
import java.util.TreeMap;

/**
 * Created by Manasvi on 6/15/15.
 *
 * Class Representing the State of the Debugger.
 * The Debugger can have multiple states at the same time,
 * but only one state is active.
 *
 * Every State has a Checkpoint History.
 *
 * A State essentially represents a specific branch in the
 * execution tree of a program.
 */
public class KDebugState {

    private NavigableMap<Integer, Checkpoint> checkpointMap;

    public KDebugState() {
        checkpointMap = new TreeMap<>();
    }

    public void addCheckpoint(Checkpoint checkpoint, int checkpointNum) {
        checkpointMap.put(checkpointNum, checkpoint);
    }
}

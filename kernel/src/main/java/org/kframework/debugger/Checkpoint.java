// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;

import org.kframework.kore.K;

/**
 * Created by Manasvi on 6/15/15.
 *
 * Class representing a Checkpoint in the State.
 *
 * Recall that the state represents a branch in the execution tree.
 * This class stores some intermediate K's encountered in that branch.
 */
public class Checkpoint {
    private K checkpointK;

    private int checkpointID;

    public K getCheckpointK() {
        return checkpointK;
    }

    public int getCheckpointID() {
        return checkpointID;
    }

    public Checkpoint(K checkpointK, int checkpointID) {
        this.checkpointK = checkpointK;
        this.checkpointID = checkpointID;
    }
}

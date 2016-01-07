// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.krun.api;

import java.util.Optional;

/**
 * Result of a step/resume operation by KRun.
 */
public class RewriteRelation {

    /**
    The final state reached.
     */
    private KRunState finalState;

    /**
    Trace of execution, with the final state
    as the last state, and the original state as root.
    Empty if computeGraph option wasn't specified as true.
     */
    private Optional<KRunGraph> executionGraph;

    public RewriteRelation(KRunState finalState, KRunGraph executionGraph) {
        this.finalState = finalState;
        this.executionGraph = Optional.ofNullable(executionGraph);
    }

    public KRunState getFinalState() {
        return finalState;
    }

    public Optional<KRunGraph> getExecutionGraph() {
        return executionGraph;
    }
}

// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.kil.Term;
import org.kframework.utils.inject.RequestScoped;

import java.io.Serializable;
import java.util.Optional;

public abstract class KRunState implements Serializable, Comparable<KRunState>, KRunResult {

    /**
    The pretty-printed term associated with this state, as suitable for display
    */
    private Term result;

    /**
    The raw term associated with this state, as suitable for further rewriting
    */
    protected Term rawResult;

    /**
     * A state ID corresponding to this state. The contract of a {@link KRun} object
     * demands that no two distinct states have the same ID. However, it does not
     * guarantee the inverse: it is the responsibility of any callers who wish
     * to ensure that the mapping is one-to-one to maintain a cache of states
     * and canonicalize the output of the KRun object.
     */
    protected int stateId;

    /**
     * Value to denote non-availability of state.
     */
    private static int NOT_AVAILABLE = -1;

    /**
     * If number of steps taken is available, then this field denotes the value.
     * Empty if data not available.
     */
    private Optional<Integer> stepsTaken;

    @RequestScoped
    public static class Counter {
        private int nextState;
    }

    public KRunState(Term rawResult, Counter counter, Optional<Integer> stepsTaken) {
        this.rawResult = rawResult;
        this.stateId = counter.nextState++;
        this.stepsTaken = stepsTaken;
    }

    public Optional<Integer> getStepsTaken() {
        return stepsTaken;
    }

    public abstract Term getRawResult();

    public Integer getStateId() {
        return stateId;
    }

    public void setStateId(Integer stateId) {
        this.stateId = stateId;
    }

    @Override
    public abstract boolean equals(Object o);

    @Override
    public abstract int hashCode();

    @Override
    public int compareTo(KRunState arg0) {
        return Integer.compare(stateId, arg0.stateId);
    }

    public abstract Term toBackendTerm();
}

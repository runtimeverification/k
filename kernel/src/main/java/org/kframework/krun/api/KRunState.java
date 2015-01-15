// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.kil.Term;

import com.google.inject.Singleton;

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
    protected Optional<Term> rawResult;

    /**
     * A state ID corresponding to this state. The contract of a {@link KRun} object
     * demands that no two distinct states have the same ID. However, it does not
     * guarantee the inverse: it is the responsibility of any callers who wish
     * to ensure that the mapping is one-to-one to maintain a cache of states
     * and canonicalize the output of the KRun object.
     */
    private int stateId;

    @Singleton
    public static class Counter {
        private int nextState;
    }

    public KRunState(Term rawResult, Counter counter) {
        this.rawResult = Optional.ofNullable(rawResult);
        this.stateId = counter.nextState++;
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
    public abstract int compareTo(KRunState arg0);
}

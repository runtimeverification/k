// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.kil.Term;
import java.io.Serializable;

public class KRunState implements Serializable, Comparable<KRunState> {

    /**
    The pretty-printed term associated with this state, as suitable for display
    */
    private Term result;

    /**
    The raw term associated with this state, as suitable for further rewriting
    */
    private Term rawResult;

    /**
     * A state ID corresponding to this state. The contract of a {@link KRun} object
     * demands that no two distinct states have the same ID. However, it does not
     * guarantee the inverse: it is the responsibility of any callers who wish
     * to ensure that the mapping is one-to-one to maintain a cache of states
     * and canonicalize the output of the KRun object.
     */
    private int stateId;

    private static int nextState = 0;

    public KRunState(Term rawResult) {
        this.rawResult = rawResult;
        this.stateId = nextState++;
    }

    public Term getRawResult() {
        return rawResult;
    }

    public Integer getStateId() {
        return stateId;
    }

    public void setStateId(Integer stateId) {
        this.stateId = stateId;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof KRunState)) return false;
        KRunState s = (KRunState)o;
        /*jung uses intensively equals while drawing graphs
          use SemanticEquals since it caches results
        */
        return SemanticEqual.checkEquality(rawResult, s.rawResult);
    }

    @Override
    public int hashCode() {
        return rawResult.hashCode();
    }

    @Override
    public int compareTo(KRunState arg0) {
        return Integer.compare(stateId, arg0.stateId);
    }
}

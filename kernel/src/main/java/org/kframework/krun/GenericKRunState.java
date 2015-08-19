// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.Term;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SemanticEqual;

import java.util.Optional;

/**
 * Generic KRunState object. Can be used for used for storing generic Terms.
 */
public class GenericKRunState extends KRunState{

    public GenericKRunState(Term term, Counter counter) {
        super(term, counter, Optional.empty());

    }
    @Override
    public Term getRawResult() {
        return rawResult;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof GenericKRunState)) {
            return false;
        }
        GenericKRunState obj = (GenericKRunState) o;
        return SemanticEqual.checkEquality(rawResult, obj.getRawResult());
    }

    @Override
    public int hashCode() {
        return rawResult.hashCode();
    }

    @Override
    public int compareTo(KRunState arg0) {
        return Integer.compare(stateId, arg0.getStateId());
    }

    @Override
    public Term toBackendTerm() {
        return rawResult;
    }
}

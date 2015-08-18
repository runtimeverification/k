// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.symbolic.BackendJavaKILtoKILTransformer;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.KRunState;

import java.util.Optional;

/**
 * Backend Specific Functionality added to the
 * Generic KRunState
 */
public class JavaKRunState extends KRunState {
    private ConstrainedTerm constrainedTerm;
    private org.kframework.backend.java.kil.Term javaTerm;

    private Context context;

    public JavaKRunState(ConstrainedTerm constrainedTerm, Context context, Counter counter, Optional<Integer> stepsTaken) {
        super(null, counter, stepsTaken);
        this.context = context;
        this.constrainedTerm = constrainedTerm;
        this.javaTerm = constrainedTerm.term();
    }

    public JavaKRunState(org.kframework.backend.java.kil.Term javaTerm, Context context, Counter counter) {
        super(null, counter, Optional.empty());
        this.context = context;
        this.javaTerm = javaTerm;
    }

    public JavaKRunState(Term term, Counter counter) {
        super(term, counter, Optional.empty());
    }


    public org.kframework.backend.java.kil.Term getJavaKilTerm() {
        return javaTerm;
    }

    public ConstrainedTerm getConstrainedTerm() {
        return constrainedTerm;
    }

    @Override
    public Term getRawResult() {
        if (rawResult != null) {
            return rawResult;
        }

        rawResult = (Term) javaTerm.accept(new BackendJavaKILtoKILTransformer(context));
        return rawResult;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof JavaKRunState)) {
            return false;
        }
        JavaKRunState state2 = (JavaKRunState) o;
        return javaTerm.equals(state2.getJavaKilTerm());

    }

    @Override
    public int hashCode() {
        return javaTerm.hashCode();
    }

    @Override
    public Term toBackendTerm() {
        return new BackendTerm(javaTerm.sort().toFrontEnd(), javaTerm);
    }
}

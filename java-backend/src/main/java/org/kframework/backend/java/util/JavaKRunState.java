// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.symbolic.BackendJavaKILtoKILTransformer;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.KRunState;

/**
 * Backend Specific Functionality added to the
 * Generic KRunState
 */
public class JavaKRunState extends KRunState{
    private ConstrainedTerm constrainedTerm;

    private Context context;

    public JavaKRunState(ConstrainedTerm constrainedTerm, Context context, Counter counter) {
        super(null, counter);
        this.context = context;
        this.constrainedTerm = constrainedTerm;
    }
    public JavaKRunState(Term term, Counter counter) {
        super(term, counter);
    }


    public org.kframework.backend.java.kil.Term getJavaKilTerm() {
        return constrainedTerm.term();
    }

    public ConstrainedTerm getConstrainedTerm() {
        return constrainedTerm;
    }

    @Override
    public Term getRawResult() {
        if (rawResult != null) {
            return rawResult;
        }
        rawResult = (Term) constrainedTerm.term().accept(new BackendJavaKILtoKILTransformer(context));
        return rawResult;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof JavaKRunState)) {
            return false;
        }
        JavaKRunState state2 = (JavaKRunState) o;
        return constrainedTerm.term().equals(state2.getJavaKilTerm());

    }

    @Override
    public int hashCode() {
        return constrainedTerm.term().hashCode();
    }
}

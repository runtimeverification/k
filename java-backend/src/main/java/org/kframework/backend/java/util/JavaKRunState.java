// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.symbolic.BackendJavaKILtoKILTransformer;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.KRunState;

/**
 * Backend Specific Functionality added to the
 * Generic KRunState
 */
public class JavaKRunState extends KRunState{
    private org.kframework.backend.java.kil.Term javaKilTerm;

    private Context context;
    public JavaKRunState(org.kframework.backend.java.kil.Term javaTerm, Context context, Counter counter) {
        super(null, counter);
        this.context = context;
        this.javaKilTerm = javaTerm;
    }

    public JavaKRunState(Term term, Counter counter) {
        super(term, counter);
    }

    public org.kframework.backend.java.kil.Term getJavaKilTerm() {
        return javaKilTerm;
    }

    @Override
    public Term getRawResult() {
        if (rawResult != null) {
            return rawResult;
        }
        rawResult = (Term) javaKilTerm.accept(new BackendJavaKILtoKILTransformer(context));
        return rawResult;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof JavaKRunState)) {
            KRunState genericObj = (KRunState) o;
            genericObj.getRawResult().equals(this.getRawResult());
        }
        JavaKRunState state2 = (JavaKRunState) o;
        return javaKilTerm.equals(state2.getJavaKilTerm());

    }

    @Override
    public int hashCode() {
        return javaKilTerm.hashCode();
    }

}

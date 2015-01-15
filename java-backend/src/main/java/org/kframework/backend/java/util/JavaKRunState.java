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

    public JavaKRunState(Context context, Counter counter) {
        super(null, counter);
        this.context = context;
    }

    @Override
    public Term getRawResult() {
        if (rawResult.isPresent()) {
            return rawResult.get();
        }
        return (Term) javaKilTerm.accept(new BackendJavaKILtoKILTransformer(context));
    }

    @Override
    public boolean equals(Object o) {
        return false;
    }

    @Override
    public int hashCode() {
        return 0;
    }

    @Override
    public int compareTo(KRunState arg0) {
        return 0;
    }
}

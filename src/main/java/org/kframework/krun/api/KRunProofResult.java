// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.kil.loader.Context;

public class KRunProofResult<T> extends KRunResult<T> {
    private boolean proven;

    public KRunProofResult(boolean proven, T result, Context context) {
        super(result, context);
        this.proven = proven;
    }

    public boolean isProven() {
        return proven;
    }

    @Override
    public String toString() {
        if (proven) {
            return "true";
        } else {
            return super.toString();
        }
    }
}

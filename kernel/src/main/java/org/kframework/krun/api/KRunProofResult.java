// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

public class KRunProofResult<T> implements KRunResult {
    private final boolean proven;
    private final T result;

    public KRunProofResult(boolean proven, T result) {
        this.result = result;
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
            return result.toString();
        }
    }
}

package org.kframework.backend.java.z3;

import org.kframework.backend.java.util.Z3Wrapper;

public enum Z3Status {
    SAT(1), UNSAT(-1), UNKNOWN(0);

    final int ordinal;
    Z3Status(int ordinal) {
        this.ordinal = ordinal;
    }

    public static Z3Status of(int ordinal) {
        switch(ordinal) {
            case 1:
                return SAT;
            case -1:
                return UNSAT;
            case 0:
                return UNKNOWN;
            default:
                throw new IllegalArgumentException("Illegal ordinal to Z3Status: " + ordinal);
        }
    }
}

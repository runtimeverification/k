// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

/**
 * Efficient exception with no stacktrace; used for flow-control in the
 * {@link SymbolicUnifier}.
 *
 * @author YilongL
 *
 */
public class UnificationFailure extends UnificationOrMatchingFailure {

    public static final UnificationFailure UNIFICATION_FAILURE = new UnificationFailure("unification failed");

    private UnificationFailure(String message) {
        super(message);
    }
}
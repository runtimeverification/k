// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

/**
 * Efficient exception with no stacktrace; used for flow-control in the Java
 * Rewrite Engine.
 * 
 * @author YilongL
 * 
 */
public abstract class UnificationOrMatchingFailure extends RuntimeException {
    
    public UnificationOrMatchingFailure(String message) {
        super(message);
    }
    
    @Override
    public Throwable fillInStackTrace() {
        return this;
    }
}

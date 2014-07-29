// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

public class UnsupportedBackendOptionException extends UnsupportedOperationException {
    /**
     *
     */
    private static final long serialVersionUID = 1L;

    public UnsupportedBackendOptionException() {
        super();
    }

    public UnsupportedBackendOptionException(String message){
        super(message);
    }

    public UnsupportedBackendOptionException(String message, Throwable t){
        super(message, t);
    }

    public UnsupportedBackendOptionException(Throwable t){
        super(t);
    }
}

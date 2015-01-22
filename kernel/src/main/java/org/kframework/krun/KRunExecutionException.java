// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.krun;

public class KRunExecutionException extends Exception {
    /**
     *
     */
    private static final long serialVersionUID = 1L;

    public KRunExecutionException() {
        super();
    }

    public KRunExecutionException(String message){
        super(message);
    }

    public KRunExecutionException(String message, Throwable t){
        super(message, t);
    }

    public KRunExecutionException(Throwable t){
        super(t);
    }
}

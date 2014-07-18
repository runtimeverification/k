// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors.exceptions;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

@SuppressWarnings("serial")
public class ParseFailedException extends Exception {
    KException exception;

    public ParseFailedException(KException kException) {
        exception = kException;
    }

    public ParseFailedException(ParseFailedException exception2) {
        exception = exception2.exception;
    }

    @Override
    public void printStackTrace() {
        report();
    }

    public void report() {
        GlobalSettings.kem.register(exception);
    }

    public String getMessage() {
        return exception.getMessage();
    }
}

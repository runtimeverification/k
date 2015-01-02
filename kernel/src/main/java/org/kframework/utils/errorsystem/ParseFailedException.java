// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.utils.errorsystem.KExceptionManager.KEMException;

@SuppressWarnings("serial")
public class ParseFailedException extends KEMException {
    KException exception;

    public ParseFailedException(KException kException) {
        super(kException);
        exception = kException;
    }

    public KException getKException() {
        return exception;
    }
}

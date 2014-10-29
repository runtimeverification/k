// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.utils.errorsystem.KExceptionManager.KEMException;

@SuppressWarnings("serial")
public class ParseFailedException extends KEMException {
    KException exception;

    public ParseFailedException(KException kException) {
        super(kException);
        exception = kException;
    }
}

// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.Warning;

@SuppressWarnings("serial")
public class ParseFailedException extends KEMException implements Warning {
    KException exception;

    public ParseFailedException(KException kException) {
        super(kException);
        exception = kException;
    }

    public KException getKException() {
        return exception;
    }
}

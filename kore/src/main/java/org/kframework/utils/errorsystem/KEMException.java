// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

/**
 * Thrown to indicate that the K Exception manager has terminated the application due to an error.
 *
 * @author dwightguth
 */
public class KEMException extends RuntimeException {
    public final KException exception;

    KEMException(KException e) {
        super(e.toString(), e.getException());
        this.exception = e;
    }

    @Override
    public String getMessage() {
        return exception.toString();
    }
}

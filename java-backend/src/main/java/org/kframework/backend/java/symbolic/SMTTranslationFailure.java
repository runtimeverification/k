// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

public class SMTTranslationFailure extends RuntimeException {
    public SMTTranslationFailure() {
    }

    public SMTTranslationFailure(String message) {
        super(message);
    }

    public SMTTranslationFailure(String message, Throwable cause) {
        super(message, cause);
    }

    public SMTTranslationFailure(Throwable cause) {
        super(cause);
    }

    public SMTTranslationFailure(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

/**
 * @deprecated Use {@link KExceptionManager} instead.
 */
@Deprecated
public class Error {

    /**
     * @deprecated Use {@link KExceptionManager} instead.
     */
    @Deprecated
    public static void report(String message) {
        GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message));
    }
}

// vim: noexpandtab

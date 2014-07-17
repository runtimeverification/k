// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.general;

import org.kframework.utils.errorsystem.KExceptionManager;

import com.google.inject.Inject;

public class GlobalSettings {

    /**
     * @deprecated Use injected kem instead
     */
    @Deprecated
    @Inject
    public static KExceptionManager kem;
}

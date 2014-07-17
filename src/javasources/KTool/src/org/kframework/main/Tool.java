package org.kframework.main;

import com.google.inject.Inject;

public enum Tool {
    KOMPILE, KAST, KRUN, KTEST, OTHER;

    @Inject private static Tool instance;

    @Deprecated
    public static Tool instance() {
        return instance;
    }
}

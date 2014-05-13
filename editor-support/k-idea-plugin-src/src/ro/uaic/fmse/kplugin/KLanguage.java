// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin;

import com.intellij.lang.Language;

public class KLanguage extends Language {
    public static final KLanguage INSTANCE = new KLanguage();

    private KLanguage() {
        super("K");
    }
}

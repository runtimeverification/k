// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.kframework.utils.file.JarInfo;

public class ExecNames {

    // TODO: IMO, this class is a horrible hack that needs to be removed. K3.jar should be
    // portable through file system, we already have all required classes in JAR so why not just
    // invoke required constructors instead of hardcoding paths of executables here?
    //
    // This code directly copied from old ktest.

       public static final String FILE_SEPARATOR = System.getProperty("file.separator");

    public static String getKompile() {
        return getExecutable("kompile");
    }

    public static String getKrun() {
        return getExecutable("krun");
    }

    public static String getKast() {
        return getExecutable("kast");
    }

    public static String getExecutable(String exe) {
        String os = System.getProperty("os.name").toLowerCase();
        if (os.contains("win")) {
            return JarInfo.getKBase() + FILE_SEPARATOR + "bin" + FILE_SEPARATOR + exe + ".bat";
        }
        return JarInfo.getKBase() + FILE_SEPARATOR + "bin" + FILE_SEPARATOR + exe;
    }

    public static String getKDoc() {
        return getExecutable("kdoc");
    }
}

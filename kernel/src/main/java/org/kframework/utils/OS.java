// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils;

import org.kframework.utils.errorsystem.KEMException;

public enum OS {
    OSX(true), LINUX(true), UNKNOWN(false), WINDOWS(false);

    private OS(boolean isPosix) {
        this.isPosix = isPosix;
    }

    public final boolean isPosix;

    public static OS current() {
        String osString = System.getProperty("os.name").toLowerCase();
        if (osString.contains("nix") || osString.contains("nux"))
            return OS.LINUX;
        else if (osString.contains("win"))
            return OS.WINDOWS;
        else if (osString.contains("mac"))
            return OS.OSX;
        else
            return OS.UNKNOWN;
    }

    public String getNativeExecutable(String executable) {
        if (this == UNKNOWN) {
            throw KEMException.internalError(
                    "Unknown OS type. " + System.getProperty("os.name") + " not recognized. " +
                            "Please contact K developers with details of your OS.");
        }
        if (this == WINDOWS) {
            executable = executable + ".exe";
        }
        return executable;
    }
}

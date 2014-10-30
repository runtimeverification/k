// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;

public enum OS {
    OSX(true), UNIX(true), UNKNOWN(false), WIN(false);

    private OS(boolean isPosix) {
        this.isPosix = isPosix;
    }

    public final boolean isPosix;

    public static OS current() {
        String osString = System.getProperty("os.name").toLowerCase();
        if (osString.contains("nix") || osString.contains("nux"))
            return OS.UNIX;
        else if (osString.contains("win"))
            return OS.WIN;
        else if (osString.contains("mac"))
            return OS.OSX;
        else
            return OS.UNKNOWN;
    }

    public String getNativeExecutable(String executable) {
        if (this == UNKNOWN) {
            throw KExceptionManager.internalError(
                    "Unknown OS type. " + System.getProperty("os.name") + " not recognized. " +
                    "Please contact K developers with details of your OS.");
        }
        if (this == WIN) {
            executable = executable + ".exe";
        } else {
            executable = executable + ".uexe";
        }
        return executable;
    }
}

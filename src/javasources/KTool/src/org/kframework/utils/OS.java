// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.File;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public enum OS {
    OSX(true, "macosx"), UNIX(true, "linux"), UNKNOWN(false, null), WIN(false, "cygwin");
    
    private OS(boolean isPosix, String libDir) {
        this.isPosix = isPosix;
        this.libDir = KPaths.getKBase(false) + "/lib/native/" + libDir;
    }
    
    public final boolean isPosix;
    private final String libDir;
    
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
    
    public File getNativeExecutable(String executable) {
        if (this == UNKNOWN) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, 
                    "Unknown OS type. " + System.getProperty("os.name") + " not recognized. " +
                    "Please contact K developers with details of your OS."));
        }
        if (this == WIN) {
            executable = executable + ".exe";
        }
        File f = new File(libDir, executable);
        if (isPosix) {
            f.setExecutable(true, false);
        }
        return f;
    }
}

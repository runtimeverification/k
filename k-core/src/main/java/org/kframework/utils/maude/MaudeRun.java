// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.maude;

import org.kframework.utils.file.JarInfo;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;

public class MaudeRun {

    private static String MAUDE_DIR = "lib/maude";

    /**
     * This function computes the path to a K-included version of maude. It assumes that /dist/lib/maude directory contains all maude executables. It searches for the os type and the architecture and it returns the right maude executable.
     */
    public static String initializeMaudeExecutable() {
//        if (checkLocalMaudeInstallation()) {
//            String msg = "Maude is already installed on this machine. Please remove directory k-install-dir/bin/maude/binaries to use your local maude installation. ";
//            GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.INTERNAL, msg, "File System", KPaths.getKBase(false) + "/bin/maude/binaries"));
//        }

        // get system properties: file separator, os name, os architecture
        String fileSeparator = System.getProperty("file.separator");
        String osname = System.getProperty("os.name");
        String arch = System.getProperty("os.arch");

        // set different maude executables
        String maude_win = "maude.exe";
        String maude_mac = "maude.intelDarwin";
        String maude_linux_32 = "maude.linux";
        String maude_linux_64 = "maude.linux64";

        // System.out.println("OS: |" + osname + "|" + arch + "|");
        // System.out.println(KPaths.getKBase(true));

        String maudeDir = JarInfo.getKBase(false) + fileSeparator + MAUDE_DIR;
        String maudeExe = "maude";


        if (osname.toLowerCase().contains("win")) {
            maudeExe = maudeDir + fileSeparator + maude_win;
        } else if (osname.equals("Mac OS X")) {
            maudeExe = maudeDir + fileSeparator + maude_mac;
        } else if (osname.toLowerCase().contains("linux")) {
            if (arch.toLowerCase().contains("64")) {
                maudeExe = maudeDir + fileSeparator + maude_linux_64;
            } else
                maudeExe = maudeDir + fileSeparator + maude_linux_32;
        }

        final File maude = new File(maudeExe);
        if (!maude.exists()) {
            GlobalSettings.kem.registerInternalError(
                    "Cannot execute Maude from " + maudeExe + ".");
            throw new AssertionError("unreachable");
        } else {
            if (!maude.canExecute()) {
                maude.setExecutable(true);
            }
        }

        return maudeExe;
    }
}

// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.maude;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class MaudeRun {

    static boolean internalMaude = true;

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
        String version = System.getProperty("os.version");
        String arch = System.getProperty("os.arch");

        // set different maude executables
        String maude_win = "maude.exe";
        String maude_mac_leopard = "maude.intelDarwinLeopard";
        String maude_mac = "maude.intelDarwin";
        String maude_linux_32 = "maude.linux";
        String maude_linux_64 = "maude.linux64";

        // System.out.println("OS: |" + osname + "|" + arch + "|");
        // System.out.println(KPaths.getKBase(true));

        String maudeDir = KPaths.getKBase(false) + fileSeparator + KPaths.MAUDE_DIR;
        String maudeExe = "maude";


        if (osname.toLowerCase().contains("win")) {
            // silently ignore this case
            // the user should install itself maude
            // we assume that he can execute maude from command line
            maudeExe = maudeDir + fileSeparator + maude_win;
        //} else if (osname.toLowerCase().contains("mac")) {
            // I hope this condition is strong enough
        } else if (osname.equals("Mac OS X")) {
            String[] parsedVersion = version.split("\\.");
            String subversion = parsedVersion[1];
            // if at least Snow Leopard
            if (Integer.parseInt(subversion) >= 6)
                maudeExe = maudeDir + fileSeparator + maude_mac;
            else
                maudeExe = maudeDir + fileSeparator + maude_mac_leopard;
        } else if (osname.toLowerCase().contains("linux")) {
            // in this case we assume linux
            if (arch.toLowerCase().contains("64")) {
                maudeExe = maudeDir + fileSeparator + maude_linux_64;
            } else
                maudeExe = maudeDir + fileSeparator + maude_linux_32;
        }

        final File maude = new File(maudeExe);
        if (!maude.exists()) {
            KException exception = new KException(ExceptionType.WARNING, KExceptionGroup.CRITICAL,
                    "Cannot execute Maude from " + maudeExe + ".\n" +
                            "Will assume that Maude is installed by the user such that\n" +
                            "it can be executed with no warnings using the 'maude' command.",
                    "top level", "");
            GlobalSettings.kem.register(exception);
            // if the maude binaries are not found then consider default `maude`
            internalMaude = false;
            return "maude";
        } else {
            if (!maude.canExecute()) {
                maude.setExecutable(true);
            }
        }

        return maudeExe;
    }
}

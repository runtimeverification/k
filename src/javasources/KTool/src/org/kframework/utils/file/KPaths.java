// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.file;

import org.kframework.utils.OS;

import java.io.File;
import java.io.UnsupportedEncodingException;
import java.net.URLDecoder;

public class KPaths {
    public static String windowfyPath(String file) {
        if (System.getProperty("os.name").toLowerCase().contains("win")) {
            file = file.replaceFirst("([a-zA-Z]):(.*)", "/cygdrive/$1$2");
            file = file.replaceAll("\\\\", "/");
        }
        return file;
    }

    public static String javaLibraryPath = null;
    public static String JAR_PATH = "lib/java/k3.jar";
    public static String MAUDE_DIR = "lib/maude/binaries";
    public static String MAUDE_LIB_DIR = "/lib/maude/lib";
    public static String VERSION_FILE = "/lib/version.txt";

    /**
     * Returns the K installation directory
     * 
     * @param windowfy
     *            - if true, then the path will be transformed into /cygdirve/c/... when on windows (just for maude)
     * @return The path to the K installation
     */
    public static String getKBase(boolean windowfy) {
        // String env = System.getenv("K_BASE");
        String path = new File(KPaths.class.getProtectionDomain().getCodeSource().getLocation().getPath()).getAbsolutePath();
        if (!path.endsWith(".jar"))
            path = new File(path).getParentFile().getParentFile().getParentFile().getParentFile().getAbsolutePath() + "/" + JAR_PATH;
        try {
            String decodedPath = URLDecoder.decode(path, "UTF-8");
            File parent = new File(decodedPath).getParentFile().getParentFile().getParentFile();
            if (windowfy)
                return windowfyPath(parent.getAbsolutePath());
            else
                return parent.getAbsolutePath();
        } catch (UnsupportedEncodingException e) {
            e.printStackTrace();
        }
        return null;
    }

    public static String getJavaLibraryPath() {
        if (javaLibraryPath == null) {
            javaLibraryPath = KPaths.getKBase(false) + "/lib/native";

            String arch = System.getProperty("os.arch");
            switch (OS.current()) {
                case WIN:
                    if (arch.toLowerCase().contains("64"))
                        javaLibraryPath += "/cygwin/x64";
                    else
                        javaLibraryPath += "/cygwin";
                    break;
                case OSX:
                    javaLibraryPath += "/macosx";
                    break;
                case UNIX:
                    if (arch.toLowerCase().contains("64")) {
                        javaLibraryPath += "/linux/x64";
                    } else {
                        javaLibraryPath += "/linux";
                    }
            }
        }
        return javaLibraryPath;
    }
}

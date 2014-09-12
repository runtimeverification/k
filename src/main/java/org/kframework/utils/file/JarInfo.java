// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.file;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;
import com.google.inject.Inject;

import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.JarURLConnection;
import java.net.URL;
import java.net.URLDecoder;
import java.util.Date;
import java.util.jar.Manifest;

public class JarInfo {
    public static String windowfyPath(String file) {
        if (System.getProperty("os.name").toLowerCase().contains("win")) {
            file = file.replaceFirst("([a-zA-Z]):(.*)", "/cygdrive/$1$2");
            file = file.replaceAll("\\\\", "/");
        }
        return file;
    }

    private static final String JAR_PATH = "target/release/k/lib/java/k-3.0.jar";
    public static final String MAUDE_LIB_DIR = "/lib/maude/lib";

    /**
     * Returns the K installation directory
     *
     * @param windowfy
     *            - if true, then the path will be transformed into /cygdirve/c/... when on windows (just for maude)
     * @return The path to the K installation
     */
    public static String getKBase(boolean windowfy) {
        // String env = System.getenv("K_BASE");
        String path = new File(JarInfo.class.getProtectionDomain().getCodeSource().getLocation().getPath()).getAbsolutePath();
        if (!path.endsWith(".jar"))
            path = new File(path).getParentFile().getParentFile().getAbsolutePath() + "/" + JAR_PATH;
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

    public static String getZ3PreludePath() {
        return getKBase(false) + "/include/z3/prelude.smt2";
    }

    private final KExceptionManager kem;

    @Inject
    public JarInfo(KExceptionManager kem) {
        this.kem = kem;
    }

    public void printVersionMessage() {
        try {
            URL url = JarInfo.class.getResource("versionMarker");
            JarURLConnection conn = (JarURLConnection)url.openConnection();
            Manifest mf = conn.getManifest();
            String revision = mf.getMainAttributes().getValue("Implementation-Revision");
            String branch = mf.getMainAttributes().getValue("Implementation-Branch");
            Date date = new Date(Long.parseLong(mf.getMainAttributes().getValue("Implementation-Date")));
            System.out.println("K framework version " + JarInfo.class.getPackage().getImplementationVersion());
            System.out.println("Git revision: " + revision);
            System.out.println("Git branch: " + branch);
            System.out.println("Build date: " + date.toString());
        } catch (IOException e) {
            kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL,
                    "Could not load version info. Check your build system?"));
        }
    }
}

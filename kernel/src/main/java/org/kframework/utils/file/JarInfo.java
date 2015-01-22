// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.file;

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
    private static final String JAR_PATH = "k-distribution/target/release/k/lib/java/JAR_FILENAME_PLACEHOLDER.jar";

    /**
     * Returns the K installation directory
     *
     * @return The path to the K installation
     */
    public static String getKBase() {
        // String env = System.getenv("K_BASE");
        String path = new File(JarInfo.class.getProtectionDomain().getCodeSource().getLocation().getPath()).getAbsolutePath();
        if (!path.endsWith(".jar") || new File(path).getParentFile().getName().equals("target"))
            path = new File(path).getParentFile().getParentFile().getParentFile().getAbsolutePath() + "/" + JAR_PATH;
        try {
            String decodedPath = URLDecoder.decode(path, "UTF-8");
            File parent = new File(decodedPath).getParentFile().getParentFile().getParentFile();
            return parent.getAbsolutePath();
        } catch (UnsupportedEncodingException e) {
            e.printStackTrace();
        }
        return null;
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
            throw KExceptionManager.internalError("Could not load version info. Check your build system?");
        }
    }
}

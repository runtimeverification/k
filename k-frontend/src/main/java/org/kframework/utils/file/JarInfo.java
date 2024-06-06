// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.file;

import com.google.inject.Inject;
import java.io.File;
import java.io.IOException;
import java.net.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Date;
import java.util.jar.Manifest;
import org.apache.commons.io.FileUtils;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

public class JarInfo {
  private static final String JAR_PATH =
      "k-distribution/target/release/k/lib/kframework/java/JAR_FILENAME_PLACEHOLDER.jar";

  /**
   * Returns the K installation directory
   *
   * @return The path to the K installation
   */
  public static String getKBase() {
    // String env = System.getenv("K_BASE");
    String path =
        new File(JarInfo.class.getProtectionDomain().getCodeSource().getLocation().getPath())
            .getAbsolutePath();
    if (!path.endsWith(".jar") || new File(path).getParentFile().getName().equals("target"))
      path =
          new File(path).getParentFile().getParentFile().getParentFile().getAbsolutePath()
              + "/"
              + JAR_PATH;
    String decodedPath = URLDecoder.decode(path, StandardCharsets.UTF_8);
    File parent =
        new File(decodedPath).getParentFile().getParentFile().getParentFile().getParentFile();
    return parent.getAbsolutePath();
  }

  /**
   * Returns the absolute path of the includes directory. Paths are computed relative to the
   * location this class is running from. When it is run from a jar file it assumes it is in a k
   * installation at lib/java/*.jar. When it is run from a .class file it assumes it is running
   * within the K source project, from a class in k-frontend/target/classes/, and returns a path to
   * k-distribution/include
   *
   * @return
   */
  public static Path getKIncludeDir() {
    Path path;
    try {
      path = Paths.get(JarInfo.class.getProtectionDomain().getCodeSource().getLocation().toURI());
    } catch (URISyntaxException e) {
      return null;
    }
    if (!path.toFile().getAbsolutePath().endsWith(".jar")
        || path.getParent().getFileName().toString().equals("target")) {
      return path.getParent().resolve("../../k-distribution/include/kframework");
    } else {
      return path.getParent().resolve("../../../include/kframework");
    }
  }

  private final KExceptionManager kem;

  @Inject
  public JarInfo(KExceptionManager kem) {
    this.kem = kem;
  }

  public void printVersionMessage() {
    String kBase = getKBase();
    URL url = JarInfo.class.getResource("versionMarker");
    try {
      URLConnection conn = url.openConnection();
      Manifest mf = ((JarURLConnection) conn).getManifest();

      String versionDate =
          new Date(Long.parseLong(mf.getMainAttributes().getValue("Implementation-Date")))
              .toString();

      // Use the output of 'git describe' if we're building K from a Git repository, or fall back to
      // the release version if we're not (e.g. from a release tarball).
      String version = mf.getMainAttributes().getValue("Implementation-Git-Describe");
      if (version.isEmpty()) {
        version =
            "v" + FileUtils.readFileToString(new File(kBase + "/lib/kframework/version")).trim();
      }

      System.out.println("K version:    " + version);
      System.out.println("Build date:   " + versionDate);
    } catch (IOException e) {
      throw KEMException.internalError("Could not load version info.");
    }
  }
}

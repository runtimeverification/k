// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils;

import java.util.Arrays;
import java.util.List;
import org.kframework.utils.errorsystem.KEMException;

public enum OS {
  OSX(true),
  LINUX(true),
  UNKNOWN(false),
  WINDOWS(false);

  OS(boolean isPosix) {
    this.isPosix = isPosix;
  }

  public final boolean isPosix;

  public static OS current() {
    String osString = System.getProperty("os.name").toLowerCase();
    if (osString.contains("nix") || osString.contains("nux")) return OS.LINUX;
    else if (osString.contains("win")) return OS.WINDOWS;
    else if (osString.contains("mac")) return OS.OSX;
    else return OS.UNKNOWN;
  }

  public String getSharedLibraryExtension() {
    if (this == OSX) {
      return ".dylib";
    } else if (this == LINUX) {
      return ".so";
    } else {
      throw KEMException.internalError(
          "Shared libraries are not supported on: " + System.getProperty("os.name"));
    }
  }

  public List<String> getSharedLibraryCompilerFlags() {
    return Arrays.asList("-fPIC", "-shared");
  }
}

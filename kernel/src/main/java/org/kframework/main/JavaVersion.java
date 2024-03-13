// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.main;

/** Created by dwightguth on 9/23/15. */
public class JavaVersion {

  /**
   * Prints a version string that can be parsed by checkJava.
   *
   * <p>For more context on what format is expected here, see the checkJava script. If the output of
   * `java --version` ever changes, this class should do so as well.
   */
  public static void main(String[] args) {
    System.err.println("java " + System.getProperty("java.version"));
    System.err.println(System.getProperty("sun.arch.data.model") + "-Bit");
  }
}

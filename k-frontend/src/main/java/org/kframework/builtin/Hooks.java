// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.builtin;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

public class Hooks {
  public static final String BOOL = "BOOL";
  public static final String BUFFER = "BUFFER";
  public static final String BYTES = "BYTES";
  public static final String FFI = "FFI";
  public static final String FLOAT = "FLOAT";
  public static final String INT = "INT";
  public static final String IO = "IO";
  public static final String KEQUAL = "KEQUAL";
  public static final String KREFLECTION = "KREFLECTION";
  public static final String LIST = "LIST";
  public static final String MAP = "MAP";
  public static final String RANGEMAP = "RANGEMAP";
  public static final String MINT = "MINT";
  public static final String SET = "SET";
  public static final String STRING = "STRING";
  public static final String SUBSTITUTION = "SUBSTITUTION";
  public static final String UNIFICATION = "UNIFICATION";
  public static final String JSON = "JSON";

  public static final Set<String> namespaces =
      Collections.unmodifiableSet(
          new HashSet<>(
              Arrays.asList(
                  BOOL,
                  BUFFER,
                  BYTES,
                  FFI,
                  FLOAT,
                  INT,
                  IO,
                  KEQUAL,
                  KREFLECTION,
                  LIST,
                  MAP,
                  RANGEMAP,
                  MINT,
                  SET,
                  STRING,
                  SUBSTITUTION,
                  UNIFICATION,
                  JSON)));
}

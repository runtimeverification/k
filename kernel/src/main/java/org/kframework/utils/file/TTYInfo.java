// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.file;

/**
 * Encapsulates information about whether stdin, stdout, and stderr are connected to terminals.
 * Essentially, each boolean in this class is true if and only if the corresponding stream is one
 * for which ultimately the isatty function returns true.
 *
 * @author dwightguth
 */
public record TTYInfo(boolean stdin, boolean stdout, boolean stderr) {}

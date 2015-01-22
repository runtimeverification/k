// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.file;

/**
 * Encapsulates information about whether stdin, stdout, and stderr are
 * connected to terminals. Essentially, each boolean in this class is
 * true if and only if the corresponding stream is one for which
 * ultimately the isatty function returns true.
 * @author dwightguth
 *
 */
public class TTYInfo {

    public final boolean stdin, stdout, stderr;

    public TTYInfo(boolean stdin, boolean stdout, boolean stderr) {
        this.stdin = stdin;
        this.stdout = stdout;
        this.stderr = stderr;
    }
}

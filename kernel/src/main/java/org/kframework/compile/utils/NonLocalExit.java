// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.utils;

public class NonLocalExit extends RuntimeException {
    public static final NonLocalExit exception = new NonLocalExit();
    public NonLocalExit() { }

    public static void RETURN() {
        throw exception;
    }

}

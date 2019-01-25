// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.main;

/**
 * Created by dwightguth on 9/23/15.
 */
public class JavaVersion {

    public static void main(String[] args) {
        System.err.println("java version \"" + System.getProperty("java.version") + "\"");
        System.err.println(System.getProperty("sun.arch.data.model") + "-Bit");
    }
}

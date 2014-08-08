// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.File;
import java.io.Serializable;

public abstract class Source implements Comparable<Source>, Serializable {
    public abstract String toString();

    public static Source of(Class<?> sourceClass) {
        return new GeneratedSource(sourceClass);
    }

    public static Source of(File filename) {
        return new FileSource(filename);
    }

    public static Source of(String optionName) {
        return new CommandLineSource(optionName);
    }

    @Override
    public int compareTo(Source o) {
        return toString().compareTo(o.toString());
    }
}

// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

/**
 * Contains functionality generic to all output modes.
 * @author dwightguth
 *
 */
public enum OutputModes {
    PROGRAM, KORE, PRETTY, KAST, BINARY, JSON, NONE;

    private String extension;
    static {
        PROGRAM.extension = "pgm";
        KORE.extension    = "kore";
        PRETTY.extension  = "kpretty";
        KAST.extension    = "kast";
        BINARY.extension  = "kbin";
        JSON.extension    = "json";
        NONE.extension    = "";
    }

    public String ext() {
        return extension;
    }
}

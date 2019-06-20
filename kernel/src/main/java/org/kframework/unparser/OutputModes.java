// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

/**
 * Contains functionality generic to all output modes.
 * @author dwightguth
 *
 */
public enum OutputModes {
    PRETTY, PROGRAM, KAST, BINARY, JSON, LATEX, KORE, NONE;

    private String extension;
    static {
        PRETTY.extension  = "kpretty";
        PROGRAM.extension = "pgm";
        KAST.extension    = "kast";
        BINARY.extension  = "kbin";
        JSON.extension    = "json";
        LATEX.extension   = "tex";
        KORE.extension    = "kore";
        NONE.extension    = "";
    }

    public String ext() {
        return extension;
    }
}

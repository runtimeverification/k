// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.unparser;

/**
 * Contains functionality generic to all output modes.
 * @author dwightguth
 *
 */
public enum OutputModes {
    PRETTY, SOUND, KAST, BINARY, JSON , NONE;

    private String extension;
    static {
        PRETTY.extension = "kpretty";
        SOUND.extension  = "ksound";
        KAST.extension   = "kast";
        BINARY.extension = "kbin";
        JSON.extension   = "json";
        NONE.extension   = "";
    }

    public String ext() {
        return extension;
    }
}

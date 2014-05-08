// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun;

public class K {

    // os specific
    public static final String userdir = System.getProperty("user.dir");
    public static final String fileSeparator = System.getProperty("file.separator");
    public static final String lineSeparator = System.getProperty("line.separator");

    //define some constants for print
    public static final String PRETTY = "pretty";
    public static final String KORE = "kore";
    public static final String COMPATIBLE = "compatible";

    private K() {}
    
    private static Tool tool;
    
    public static enum Tool {
        KOMPILE, KRUN, KAST, KTEST, OTHER
    }
    
    public static void setTool(Tool tool) {
        if (K.tool != null) {
            assert false : "Can only call setTool once";
        }
        K.tool = tool;
    }
    
    public static Tool tool() {
        return tool;
    }
}

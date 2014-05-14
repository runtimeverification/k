// Copyright (c) 2011-2014 K Team. All Rights Reserved.
package org.kframework.ktest.Config;


/**
 * See http://javacoalface.blogspot.com/2011/04/line-and-column-numbers-in-xml-dom.html
 */
public class LocationData {

    public static final String LOCATION_DATA_KEY = "locationDataKey";

    private final String systemId;
    private final int startLine;
    private final int startColumn;
    private final int endLine;
    private final int endColumn;

    public LocationData(String systemId, int startLine,
                        int startColumn, int endLine, int endColumn) {
        super();
        this.systemId = systemId;
        this.startLine = startLine;
        this.startColumn = startColumn;
        this.endLine = endLine;
        this.endColumn = endColumn;
    }

    public LocationData() {
        systemId = null;
        startLine = -1;
        startColumn = -1;
        endLine = -1;
        endColumn = -1;
    }

    public String getSystemId() {
        return systemId;
    }

    public int getStartLine() {
        return startLine;
    }

    public int getStartColumn() {
        return startColumn;
    }

    public boolean isCmdLine() {
        return systemId == null;
    }

    public int getEndLine() {
        return endLine;
    }

    public int getEndColumn() {
        return endColumn;
    }

    @Override
    public String toString() {
        if (systemId == null)
            return "command line";
        return getSystemId() + getPosStr();
    }

    public String getPosStr() {
        if (startLine == -1 || startColumn == -1 || endLine == -1 || endColumn == -1)
            return "";
        return "[line " + startLine + ":"
                + startColumn + " to line " + endLine + ":"
                + endColumn + "]";
    }
}
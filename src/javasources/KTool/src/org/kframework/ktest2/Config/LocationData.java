package org.kframework.ktest2.Config;


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
    private final boolean isCmdLine;

    public LocationData(String systemId, int startLine,
                        int startColumn, int endLine, int endColumn) {
        super();
        this.systemId = systemId;
        this.startLine = startLine;
        this.startColumn = startColumn;
        this.endLine = endLine;
        this.endColumn = endColumn;
        this.isCmdLine = false;
    }

    public LocationData() {
        systemId = null;
        startLine = -1;
        startColumn = -1;
        endLine = -1;
        endColumn = -1;
        this.isCmdLine = true;
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
        return isCmdLine;
    }

    public int getEndLine() {
        return endLine;
    }

    public int getEndColumn() {
        return endColumn;
    }

    @Override
    public String toString() {
        return getSystemId() + getPosStr();
    }

    public String getPosStr() {
        return "[line " + startLine + ":"
                + startColumn + " to line " + endLine + ":"
                + endColumn + "]";
    }
}
// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.Serializable;

public class Location implements Comparable<Location>, Serializable {

    public Location(int lineStart, int columnStart, int lineEnd, int columnEnd) {
        this.lineStart = lineStart;
        this.lineEnd = lineEnd;
        this.columnStart = columnStart;
        this.columnEnd = columnEnd;
    }
    public int lineStart;
    public int columnStart;
    public int lineEnd;
    public int columnEnd;

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + columnEnd;
        result = prime * result + columnStart;
        result = prime * result + lineEnd;
        result = prime * result + lineStart;
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Location other = (Location) obj;
        if (columnEnd != other.columnEnd)
            return false;
        if (columnStart != other.columnStart)
            return false;
        if (lineEnd != other.lineEnd)
            return false;
        if (lineStart != other.lineStart)
            return false;
        return true;
    }

    @Override
    public String toString() {
        return "(" + lineStart + "," + columnStart + "," + lineEnd + "," + columnEnd + ")";
    }

    @Override
    public int compareTo(Location arg) {
        int x;
        if ((x = Integer.compare(lineStart, arg.lineStart)) != 0)
            return x;
        if ((x = Integer.compare(columnStart, arg.columnStart)) != 0)
            return x;
        if ((x = Integer.compare(lineEnd, arg.lineEnd)) != 0)
            return x;
        if ((x = Integer.compare(columnEnd, arg.columnEnd)) != 0)
            return x;
        return 0;
    }

}

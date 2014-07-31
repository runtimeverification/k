// Copyright (c) 2011-2014 K Team. All Rights Reserved.
package org.kframework.ktest.Config;

import java.io.File;

import org.kframework.kil.Location;


/**
 * See http://javacoalface.blogspot.com/2011/04/line-and-column-numbers-in-xml-dom.html
 */
public class LocationData {

    public static final String LOCATION_DATA_KEY = "locationDataKey";

    private final File file;
    private final Location location;

    public LocationData(String systemId, int startLine,
            int startColumn, int endLine, int endColumn) {
        super();
        this.location = new Location(startLine, startColumn, endLine, endColumn);
        this.file = new File(systemId);
    }

    public LocationData() {
        file = null;
        location = null;
    }

    public File getFile() {
        return file;
    }

    public Location getLocation() {
        return location;
    }
}
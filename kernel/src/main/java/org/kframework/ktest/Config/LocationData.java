// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.ktest.Config;

import java.io.File;

import org.kframework.kil.Location;
import org.kframework.kil.Source;
import org.kframework.kil.Sources;


/**
 * See http://javacoalface.blogspot.com/2011/04/line-and-column-numbers-in-xml-dom.html
 */
public class LocationData {

    public static final String LOCATION_DATA_KEY = "locationDataKey";

    private final Source source;
    private final Location location;

    public LocationData(File systemId, int startLine,
            int startColumn, int endLine, int endColumn) {
        super();
        this.location = new Location(startLine, startColumn, endLine, endColumn);
        this.source = Sources.fromFile(systemId);
    }

    public LocationData() {
        source = null;
        location = null;
    }

    public Source getSource() {
        return source;
    }

    public Location getLocation() {
        return location;
    }
}
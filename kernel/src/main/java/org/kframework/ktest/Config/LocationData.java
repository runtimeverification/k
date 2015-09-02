// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.ktest.Config;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

import java.io.File;

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
        this.source = Source.apply(systemId.getAbsolutePath());
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
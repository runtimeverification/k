// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.ktest.Config;

public class InvalidConfigError extends Throwable {

    private final LocationData location;

    public InvalidConfigError(String msg, LocationData location) {
        super(msg);
        this.location = location;
    }

    public LocationData getLocation() {
        return location;
    }
}

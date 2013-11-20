package org.kframework.ktest2.Config;

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

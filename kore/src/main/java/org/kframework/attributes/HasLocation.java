// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.attributes;

import java.util.Optional;

public interface HasLocation {
    Optional<Location> location();
    Optional<Source> source();
}

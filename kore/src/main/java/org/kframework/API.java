// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

/**
 * Marker for classes we consider as part fo the K API.
 * It is particularly important for these classes to be well-documented.
 */
@Target(ElementType.TYPE)
public @interface API {

}

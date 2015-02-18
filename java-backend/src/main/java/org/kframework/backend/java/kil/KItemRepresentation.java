// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;


public interface KItemRepresentation extends KoreRepresentation {
    default Term kLabel() {
        return ((KItem) toKore()).kLabel();
    }

    default Term kList() {
        return ((KItem) toKore()).kLabel();
    }
}

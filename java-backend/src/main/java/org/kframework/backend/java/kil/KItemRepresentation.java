// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;


public interface KItemRepresentation extends KoreRepresentation {
    default Term kLabel(TermContext context) {
        return ((KItem) toKore(context)).kLabel();
    }

    default Term kList(TermContext context) {
        return ((KItem) toKore(context)).kLabel();
    }
}

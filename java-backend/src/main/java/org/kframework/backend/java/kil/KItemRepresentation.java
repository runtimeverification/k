// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;


import org.kframework.kore.*;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;

public interface KItemRepresentation extends KoreRepresentation, KApply {
    default Term kLabel() {
        return ((KItem) toKore()).kLabel();
    }

    default Term kList() {
        return ((KItem) toKore()).kList();
    }

    default org.kframework.kore.KLabel klabel() {
        return (KLabel) kLabel();
    }

    default org.kframework.kore.KList klist() {
        return (KList) kList();
    }
}

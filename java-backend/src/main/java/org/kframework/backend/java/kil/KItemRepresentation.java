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

    @Override
    default org.kframework.kore.KLabel klabel() {
        if (kLabel() instanceof KLabelInjection) {
            return ((KApply) ((KLabelInjection) kLabel()).term()).klabel();
        } else {
            return (KLabel) kLabel();
        }
    }

    @Override
    default org.kframework.kore.KList klist() {
        if (kLabel() instanceof KLabelInjection) {
            return ((KApply) ((KLabelInjection) kLabel()).term()).klist();
        } else {
            return (KList) kList();
        }
    }
}
